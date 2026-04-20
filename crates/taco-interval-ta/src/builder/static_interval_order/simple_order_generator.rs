//! This module contains the implementation of the interval boundary ordering
//! algorithm. To generate all possible interval boundary orders that are
//! satisfiable, create an `SimpleOrderGeneratorContext` and extend it with the
//! interval boundaries of the individual variables.
//!
//! # Algorithm
//!
//! This algorithm currently takes a very simple approach:
//!     1.  Insert the interval borders 0 and 1 to the list of intervals for
//!         each variable (upon first insertion of an interval).
//!     2.  Generate all orders where the new interval is equal to an existing
//!         one: For each known interval of the variable, create the
//!         IncompleteOrder in which the new intervals is considered equal
//!     3.  Generate all possible strict orders: Insert the new interval at each
//!         possible point in the order
//!     4.  Filter unsatisfiable orders by encoding the order into SMT along
//!         with the resilience condition
//!
//! This algorithm is currently very expensive: We explicitly generate all
//! permutations and check each of them with the SMT solver.

use core::fmt;
use std::{collections::HashMap, rc::Rc};

use taco_display_utils::join_iterator;
use taco_smt_encoder::{
    SMTExpr, SMTSolver, SMTSolverBuilder, SMTSolverContext,
    expression_encoding::{
        EncodeToSMT, SMTSolverError, SMTVariableContext, StaticSMTContext,
        ta_encoding::encode_resilience_condition,
    },
};
use taco_threshold_automaton::{
    ThresholdAutomaton,
    expressions::{BooleanExpression, ComparisonOp, Parameter, Variable},
    lia_threshold_automaton::integer_thresholds::{IntoNoDivBooleanExpr, WeightedSum},
};

use crate::HasAssociatedIntervals;

use super::{Interval, IntervalBoundary, StaticIntervalOrder};

/// Context for generating all satisfiable orders of interval boundaries
///
/// This context can be used to generate all possible orders of interval
/// boundaries that are consistent with the resilience condition of the given
/// threshold automaton. All generated orders are guaranteed to be satisfiable.
///
/// Generating these orders and checking their satisfiability is done with the
/// help of an SMT solver.
pub struct SimpleOrderGeneratorContext {
    /// SMT solver context
    solver: StaticSMTContext,
    /// Currently known incomplete orders
    incomplete_orders: Vec<IncompleteOrder>,
}

impl SimpleOrderGeneratorContext {
    /// Create a new OrderGeneratorContext for
    pub fn new<T: ThresholdAutomaton>(ta: &T, solver_builder: SMTSolverBuilder) -> Self {
        let mut ctx = StaticSMTContext::new(
            solver_builder,
            ta.parameters().cloned(),
            Vec::new(),
            Vec::new(),
        )
        .expect("Failed to create SMT context for interval ordering");

        // assert that all parameters are >= 0
        if ta.parameters().count() > 0 {
            let expr = ctx.get_smt_solver().and_many(ta.parameters().map(|p| {
                ctx.get_smt_solver().gte(
                    ctx.get_expr_for(p).unwrap(),
                    ctx.get_smt_solver().numeral(0),
                )
            }));
            ctx.get_smt_solver_mut()
                .assert(expr)
                .expect("failed to assert parameters gt 0");
        }

        let rc = encode_resilience_condition(ta, ctx.get_smt_solver(), &ctx);
        ctx.get_smt_solver_mut()
            .assert(rc)
            .expect("Failed to encode resilience condition");

        Self {
            solver: ctx,
            incomplete_orders: vec![IncompleteOrder::new()],
        }
    }

    /// Extend all orders with the interval boundary for the given variable
    pub fn extend_order_with_interval_for_single_variable(
        mut self,
        var: &Variable,
        ib: &IntervalBoundary,
    ) -> SimpleOrderGeneratorContext {
        self.incomplete_orders = self
            .incomplete_orders
            .into_iter()
            .flat_map(|order| order.extend(var, ib, &mut self.solver))
            .collect();

        self
    }

    /// Extend all orders with the interval boundary for the given variable
    pub fn extend_order_with_interval_for_multi_variable(
        mut self,
        var: &WeightedSum<Variable>,
        ib: &IntervalBoundary,
    ) -> SimpleOrderGeneratorContext {
        self.incomplete_orders = self
            .incomplete_orders
            .into_iter()
            .flat_map(|order| order.extend(var, ib, &mut self.solver))
            .collect();
        self
    }

    /// Build all orders
    ///
    /// Build all possible orders from the currently known incomplete orders and
    /// add the intervals 0 and 1 for each variable that is not already known.
    pub fn build_orders(mut self, vars: &[Variable]) -> Vec<StaticIntervalOrder> {
        self.incomplete_orders
            .into_iter()
            .map(|order| order.complete(&mut self.solver, vars.iter()))
            .collect()
    }
}

/// A satisfiable ordering of interval boundaries that can possibly be
/// incomplete

#[derive(Debug, Clone, PartialEq)]
struct IncompleteOrder {
    /// List of tuples denoting which interval boundaries are considered equal
    equal_boundaries: Vec<(Rc<IntervalBoundary>, Vec<Rc<IntervalBoundary>>)>,
    /// Stores the current fixed ordering
    single_variable_order: HashMap<Variable, Vec<Rc<IntervalBoundary>>>,
    /// Stores the current fixed ordering
    multi_variable_order: HashMap<WeightedSum<Variable>, Vec<Rc<IntervalBoundary>>>,
}

impl IncompleteOrder {
    /// Create a new empty incomplete ordering
    pub fn new() -> Self {
        Self {
            equal_boundaries: Vec::new(),
            single_variable_order: HashMap::new(),
            multi_variable_order: HashMap::new(),
        }
    }

    /// Transform the incomplete order into a static order and a list of
    /// interval borders which are considered to be equal.
    ///
    /// This function should be called when all interval boundaries are inserted
    /// into the order
    fn complete<'a>(
        mut self,
        ctx: &mut StaticSMTContext,
        vars: impl Iterator<Item = &'a Variable>,
    ) -> StaticIntervalOrder {
        debug_assert!(
            self.check_satisfiable(ctx),
            "Only satisfiable orders should have been generated"
        );

        vars.for_each(|var| {
            if !self.single_variable_order.contains_key(var) {
                self.single_variable_order.insert(
                    var.clone(),
                    Vec::from([
                        Rc::new(IntervalBoundary::from_const(0)),
                        Rc::new(IntervalBoundary::from_const(1)),
                    ]),
                );
            }
        });

        let single_var_ib = self
            .single_variable_order
            .into_iter()
            .map(|(var, intervals)| {
                (
                    var,
                    Self::interval_boundaries_to_intervals(
                        intervals.into_iter().map(|i| i.as_ref().clone()),
                    ),
                )
            })
            .collect();

        let multi_var_ib = self
            .multi_variable_order
            .into_iter()
            .map(|(var, intervals)| {
                (
                    var,
                    Self::interval_boundaries_to_intervals(
                        intervals.into_iter().map(|i| i.as_ref().clone()),
                    ),
                )
            })
            .collect();

        let equal_ib = self
            .equal_boundaries
            .into_iter()
            .flat_map(|(to_replace_with, intervals_to_replace)| {
                intervals_to_replace
                    .into_iter()
                    .map(move |interval_to_replace| {
                        (
                            interval_to_replace.as_ref().clone(),
                            to_replace_with.as_ref().clone(),
                        )
                    })
            })
            .collect();

        StaticIntervalOrder {
            single_var_order: single_var_ib,
            multi_var_order: multi_var_ib,
            equal_boundaries: equal_ib,
        }
    }

    /// Transform an iterator over interval boundaries into a vector of intervals
    fn interval_boundaries_to_intervals(
        mut it: impl Iterator<Item = IntervalBoundary>,
    ) -> Vec<Interval> {
        let previous_border = it.next();
        if previous_border.is_none() {
            return Vec::new();
        }

        let mut previous_border = previous_border.unwrap();
        let mut intervals = Vec::new();

        for border in it {
            intervals.push(Interval::new(previous_border, false, border.clone(), true));
            previous_border = border;
        }

        intervals.push(Interval::new(
            previous_border,
            false,
            IntervalBoundary::new_infty(),
            true,
        ));

        intervals
    }

    fn checked_add_constraint_boundary_equal(
        mut self,
        known_ib: &Rc<IntervalBoundary>,
        new_ib: &Rc<IntervalBoundary>,
    ) -> Self {
        // Known boundary exists in order
        debug_assert!(
            self.single_variable_order
                .iter()
                .any(|(_, boundaries)| boundaries.contains(known_ib))
                || self
                    .multi_variable_order
                    .iter()
                    .any(|(_, boundaries)| boundaries.contains(known_ib))
        );
        // New one does not exist yet
        debug_assert!(
            !self.equal_boundaries.iter().any(|(ib, _)| ib == new_ib),
            "Should have been replaced! Order {self}"
        );
        debug_assert!(
            !self
                .equal_boundaries
                .iter()
                .any(|(_, ibs)| ibs.contains(new_ib)),
            "Should have been replaced! Order {self}"
        );

        for ibs in self.equal_boundaries.iter_mut() {
            if ibs.0 == *known_ib {
                ibs.1.push(new_ib.clone());
                return self;
            }
        }

        self.equal_boundaries
            .push((known_ib.clone(), vec![new_ib.clone()]));
        self
    }

    /// This function is a helper function for the encode_to_smt function.
    ///
    /// It takes the current order of interval boundaries and encodes the order
    /// into an SMT expression by requiring that each interval boundary is
    /// strictly smaller than the next one.
    fn encode_smt_interval_boundary_order<'b>(
        &'b self,
        ctx: &(impl SMTSolverContext + SMTVariableContext<Variable> + SMTVariableContext<Parameter>),
        it: impl Iterator<Item = &'b Vec<Rc<IntervalBoundary>>>,
    ) -> Result<SMTExpr, SMTSolverError> {
        let res = it
            .map(|borders| {
                if borders.is_empty() || borders.len() == 1 {
                    return Ok::<_, SMTSolverError>(ctx.get_smt_solver().true_());
                }

                let mut curr_border = borders[0]
                    .get_threshold()
                    .expect("Infinite interval in order");
                let mut conditions = Vec::with_capacity(borders.len() - 1);

                for next_border in borders
                    .iter()
                    .map(|ib| ib.get_threshold().expect("Infinite interval in order"))
                    .skip(1)
                {
                    let constr: BooleanExpression<Parameter> = curr_border
                        .encode_comparison_to_boolean_expression(ComparisonOp::Lt, next_border);
                    conditions.push(constr);
                    curr_border = next_border;
                }

                // collect SMT expression for each interval boundary
                let smt_borders = conditions
                    .into_iter()
                    .map(|border_expr| {
                        border_expr.encode_to_smt_with_ctx(ctx.get_smt_solver(), ctx)
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                Ok(ctx.get_smt_solver().and_many(smt_borders))
            })
            .collect::<Result<Vec<_>, _>>()?;

        // if there are no interval boundaries, return true (easy_smt panics otherwise)
        if res.is_empty() {
            return Ok(ctx.get_smt_solver().true_());
        }

        Ok(ctx.get_smt_solver().and_many(res))
    }

    /// This function is a helper function for the encode_to_smt function.
    ///
    /// It takes a set of intervals that are considered to be equal and encodes
    /// the equality constraints into an SMT expression.
    fn encode_smt_equality_constraint<'b>(
        &'b self,
        ctx: &(impl SMTSolverContext + SMTVariableContext<Variable> + SMTVariableContext<Parameter>),
        it: impl Iterator<Item = &'b (Rc<IntervalBoundary>, Vec<Rc<IntervalBoundary>>)>,
    ) -> Result<SMTExpr, SMTSolverError> {
        let eq_ibs = it
            .map(|(first_ib, equal_ibs)| {
                // threshold of first interval boundary
                let first_ib_thr = first_ib
                    .get_threshold()
                    .expect("Infinite interval in order");

                let eq_exprs = equal_ibs
                    .iter()
                    .map(|ib| ib.get_threshold().expect("Infinite interval in order"))
                    .map(|ib_thr| {
                        first_ib_thr
                            .encode_comparison_to_boolean_expression(ComparisonOp::Eq, ib_thr)
                    })
                    .map(|bexpr: BooleanExpression<Parameter>| {
                        bexpr.encode_to_smt_with_ctx(ctx.get_smt_solver(), ctx)
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                Ok::<_, SMTSolverError>(ctx.get_smt_solver().and_many(eq_exprs))
            })
            .collect::<Result<Vec<_>, _>>()?;

        // if there are no interval boundaries, return true (easy_smt panics otherwise)
        if eq_ibs.is_empty() {
            return Ok(ctx.get_smt_solver().true_());
        }

        Ok(ctx.get_smt_solver().and_many(eq_ibs))
    }
}

impl<C> EncodeToSMT<IncompleteOrder, C> for IncompleteOrder
where
    C: SMTVariableContext<Variable> + SMTVariableContext<Parameter> + SMTSolverContext,
{
    /// Encodes the constructed incomplete order into an SMT expression
    ///
    /// Encodes the incomplete order into an SMT expression. This constraint allows
    /// to asses whether a given partial order is consistent with the resilience
    /// condition. If this expression is unsatisfiable, any partial order that
    /// extends the current partial order is also unsatisfiable.
    fn encode_to_smt_with_ctx(
        &self,
        _solver: &SMTSolver,
        ctx: &C,
    ) -> Result<SMTExpr, SMTSolverError> {
        // Encode the equality constraints
        let eq_ibs = self.encode_smt_equality_constraint(ctx, self.equal_boundaries.iter())?;

        // Encode the known order for single variables
        let known_order_single =
            self.encode_smt_interval_boundary_order(ctx, self.single_variable_order.values())?;

        // Encode the known order for a sum over variables
        let known_order_multi =
            self.encode_smt_interval_boundary_order(ctx, self.multi_variable_order.values())?;

        Ok(ctx
            .get_smt_solver()
            .and_many(vec![eq_ibs, known_order_single, known_order_multi]))
    }
}

/// Internal trait defining how to access order for `T`
trait StoresIntervalOrder<T: HasAssociatedIntervals>: DeriveModifiedOrdering + Sized + Clone {
    /// Get a reference to the current order
    fn get_order(&self) -> &HashMap<T, Vec<Rc<IntervalBoundary>>>;
    /// Get a mutable reference to the current order
    fn get_order_mut(&mut self) -> &mut HashMap<T, Vec<Rc<IntervalBoundary>>>;

    /// Extend the order by adding a new interval boundary
    ///
    /// This function implements the main algorithm for ordering the interval
    /// boundaries. It computes all possible extensions of the order, checks for
    /// satisfiability and returns all valid orderings.
    ///
    /// Call this function for every variable, interval boundary pair before
    /// using build.
    ///
    /// # Arguments
    ///
    /// - `interval`: new interval boundary to add to the order
    /// - `var`: variable for which the interval is added
    /// - `ctx`: SMTSolver context **already containing the encoded resilience
    ///   condition** to use when checking for satisfiability
    fn extend(
        mut self,
        var: &T,
        boundary: &IntervalBoundary,
        ctx: &mut (impl SMTSolverContext + SMTVariableContext<Variable> + SMTVariableContext<Parameter>),
    ) -> Vec<Self> {
        let mut boundary = Rc::new(boundary.clone());
        let mut already_considered_equalities = true;

        if let Some(known_boundary) = self.check_boundary_already_in_eq_constraint(&boundary) {
            boundary = known_boundary;
            already_considered_equalities = false;
        }

        // Check whether the interval is already known for this variable and
        // therefore we can skip it as it must have been already ordered
        // Also: if the variable is not known insert boundaries 0 and 1
        if self
            .get_order_mut()
            .entry(var.clone())
            .or_insert(Vec::from([
                Rc::new(IntervalBoundary::from_const(0)),
                Rc::new(IntervalBoundary::from_const(1)),
            ]))
            .contains(&boundary)
        {
            return vec![self];
        }

        let mut discovered_orders = Vec::new();
        // if we already have an equality constraint, we already considered all possible equalities
        if already_considered_equalities {
            discovered_orders = self
                .clone()
                .compute_all_possible_equality_extensions(var, &boundary, ctx)
        }

        // Assume the interval is not equal to any known interval
        // Generate all possibilities of where the interval could be inserted
        // and check whether the order is satisfiable
        let mut found_satisfiable = false;
        for i in 0..self.get_order().get(var).unwrap().len() + 1 {
            let mut new_order = self.clone();
            new_order
                .get_order_mut()
                .get_mut(var)
                .unwrap()
                .insert(i, boundary.clone());

            if new_order.check_satisfiable(ctx) {
                discovered_orders.push(new_order);
                found_satisfiable = true;
                continue;
            }

            // by transitivity all following orders will be unsatisfiable,
            // therefore terminate early
            if found_satisfiable {
                break;
            }
        }

        discovered_orders
    }

    /// Construct all orders in which boundary is equal to a boundary already
    /// ordered for `var`, then returns all orders that were satisfiable
    fn compute_all_possible_equality_extensions(
        self,
        var: &T,
        ib: &Rc<IntervalBoundary>,
        ctx: &mut (impl SMTSolverContext + SMTVariableContext<Variable> + SMTVariableContext<Parameter>),
    ) -> Vec<Self> {
        // For every interval that is known for variable `var`, assume that it
        // can be equal to boundary
        self.get_order()
            .get(var)
            .unwrap()
            .iter()
            .map(|known_ib| self.clone().add_constraint_boundary_equal(known_ib, ib))
            .filter(|ord| ord.check_satisfiable(ctx))
            .collect()
    }
}

/// This trait is used to implement common functionality of an
/// `IncompleteOrdering` that is independent from the type for which the
/// intervals are defined
trait DeriveModifiedOrdering {
    /// Check if the boundary needs to be replaced because it appears in an
    /// equality constraint
    fn check_boundary_already_in_eq_constraint(
        &self,
        i: &Rc<IntervalBoundary>,
    ) -> Option<Rc<IntervalBoundary>>;
    /// Encode the current order into an SMT constraint and check whether there
    /// exist a satisfying assignment for it in the current context
    fn check_satisfiable(
        &self,
        ctx: &mut (impl SMTSolverContext + SMTVariableContext<Variable> + SMTVariableContext<Parameter>),
    ) -> bool;
    /// Add a constraint to the current order that assumes that
    /// `known_boundary` is equal to `new_boundary`
    ///
    /// # Arguments
    ///
    /// - `known_boundary`: boundary already contained in the order
    /// - `new_boundary`: boundary to add, not appearing in order yet
    fn add_constraint_boundary_equal(
        self,
        known_ib: &Rc<IntervalBoundary>,
        new_ib: &Rc<IntervalBoundary>,
    ) -> Self;
}

impl DeriveModifiedOrdering for IncompleteOrder {
    fn check_boundary_already_in_eq_constraint(
        &self,
        i: &Rc<IntervalBoundary>,
    ) -> Option<Rc<IntervalBoundary>> {
        if let Some((replace, _)) = self
            .equal_boundaries
            .iter()
            .find(|(replace, bucket)| replace == i || bucket.contains(i))
        {
            return Some(replace.clone());
        }

        None
    }

    fn check_satisfiable(
        &self,
        ctx: &mut (impl SMTSolverContext + SMTVariableContext<Variable> + SMTVariableContext<Parameter>),
    ) -> bool {
        let valid_query = self
            .encode_to_smt_with_ctx(ctx.get_smt_solver(), ctx)
            .expect("Failed to encode ordering for interval ordering");

        // create a new frame for the query
        ctx.get_smt_solver_mut()
            .push()
            .expect("Failed to create new SMT frame");

        let res = ctx
            .assert_and_check_expr(valid_query)
            .expect("Failed to verify possible ordering, SMT query failed");

        // pop the frame
        ctx.get_smt_solver_mut()
            .pop()
            .expect("Failed to pop SMT frame");

        res.is_sat()
    }

    fn add_constraint_boundary_equal(
        self,
        known_boundary: &Rc<IntervalBoundary>,
        new_boundary: &Rc<IntervalBoundary>,
    ) -> Self {
        self.checked_add_constraint_boundary_equal(known_boundary, new_boundary)
    }
}

impl StoresIntervalOrder<Variable> for IncompleteOrder {
    fn get_order(&self) -> &HashMap<Variable, Vec<Rc<IntervalBoundary>>> {
        &self.single_variable_order
    }

    fn get_order_mut(&mut self) -> &mut HashMap<Variable, Vec<Rc<IntervalBoundary>>> {
        &mut self.single_variable_order
    }
}

impl StoresIntervalOrder<WeightedSum<Variable>> for IncompleteOrder {
    fn get_order(&self) -> &HashMap<WeightedSum<Variable>, Vec<Rc<IntervalBoundary>>> {
        &self.multi_variable_order
    }

    fn get_order_mut(&mut self) -> &mut HashMap<WeightedSum<Variable>, Vec<Rc<IntervalBoundary>>> {
        &mut self.multi_variable_order
    }
}

impl fmt::Display for IncompleteOrder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "PartialOrder {{")?;

        if !self.equal_boundaries.is_empty() {
            writeln!(
                f,
                "    {},",
                join_iterator(
                    self.equal_boundaries.iter().map(|eq_bucket| format!(
                        "{} == {}",
                        eq_bucket.0,
                        join_iterator(eq_bucket.1.iter(), " == ")
                    )),
                    " && "
                )
            )?;
        }

        if !self.single_variable_order.is_empty() {
            let mut sorted_single_var = self.single_variable_order.iter().collect::<Vec<_>>();
            sorted_single_var.sort_by(|a, b| a.0.cmp(b.0));

            for (var, ibs) in sorted_single_var.iter() {
                writeln!(f, "    {}: {},", var, join_iterator(ibs.iter(), " < "))?;
            }
        }

        if !self.multi_variable_order.is_empty() {
            for (var, ibs) in self.multi_variable_order.iter() {
                writeln!(f, "    {}: {},", var, join_iterator(ibs.iter(), " < "))?;
            }
        }

        writeln!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::HashMap, rc::Rc};

    use taco_smt_encoder::{
        SMTSolverBuilder, SMTSolverContext,
        expression_encoding::{EncodeToSMT, StaticSMTContext},
    };
    use taco_threshold_automaton::{
        ThresholdAutomaton,
        expressions::{
            BooleanExpression, ComparisonOp, IntegerExpression, Location, Parameter, Variable,
            fraction::Fraction,
        },
        general_threshold_automaton::builder::GeneralThresholdAutomatonBuilder,
        lia_threshold_automaton::integer_thresholds::WeightedSum,
    };

    use crate::{
        builder::static_interval_order::{
            StaticIntervalOrder,
            simple_order_generator::{DeriveModifiedOrdering, SimpleOrderGeneratorContext},
        },
        interval::{Interval, IntervalBoundary},
    };

    use super::IncompleteOrder;

    #[test]
    fn test_encode_to_smt_partial_order() {
        let builder = SMTSolverBuilder::default();
        let ctx = StaticSMTContext::new(
            builder.clone(),
            vec![Parameter::new("n"), Parameter::new("f")],
            Vec::new(),
            Vec::new(),
        )
        .unwrap();

        let partial_order = super::IncompleteOrder {
            equal_boundaries: Vec::from([(
                Rc::new(IntervalBoundary::new_bound(
                    WeightedSum::new([(Parameter::new("f"), 1)]),
                    0,
                )),
                vec![Rc::new(IntervalBoundary::new_bound(
                    WeightedSum::new([(Parameter::new("n"), 1)]),
                    0,
                ))],
            )]),
            single_variable_order: HashMap::from([(
                Variable::new("x"),
                vec![
                    Rc::new(IntervalBoundary::from_const(0)),
                    Rc::new(IntervalBoundary::from_const(1)),
                ],
            )]),
            multi_variable_order: HashMap::new(),
        };
        let got_smt_encoding = ctx.encode_to_smt(&partial_order).unwrap();

        let eq_smt = ctx
            .encode_to_smt(&BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::<Variable>::Param(Parameter::new("f"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Param(Parameter::new("n"))),
            ))
            .unwrap();

        let known_order_smt = ctx.get_smt_solver().lt(
            ctx.get_smt_solver().numeral(0),
            ctx.get_smt_solver().numeral(1),
        );

        let expected = ctx
            .get_smt_solver()
            .and_many(vec![eq_smt, known_order_smt, ctx.get_true()]);

        // Check that the formulas are equivalent
        assert_eq!(
            got_smt_encoding,
            expected,
            "SMT encoding is not as expected. Expected: {} Got: {}",
            ctx.get_smt_solver().display(expected),
            ctx.get_smt_solver().display(got_smt_encoding)
        );
    }

    #[test]
    fn test_check_satisfiable() {
        let builder = SMTSolverBuilder::default();

        let rc = [BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Param(Parameter::new("n"))),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Const(3)),
        )];

        let ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_locations(vec![Location::new("l1"), Location::new("l2")])
            .unwrap()
            .with_parameters(vec![Parameter::new("n"), Parameter::new("f")])
            .unwrap()
            .initialize()
            .with_resilience_condition(rc[0].clone())
            .unwrap()
            .build();

        let mut ctx = StaticSMTContext::new(
            builder.clone(),
            ta.parameters().cloned(),
            Vec::new(),
            Vec::new(),
        )
        .unwrap();
        let rc = ta
            .resilience_conditions()
            .map(|rc| rc.encode_to_smt_with_ctx(ctx.get_smt_solver(), &ctx))
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let rc = ctx.get_smt_solver().and_many(rc);
        ctx.get_smt_solver_mut().assert(rc).unwrap();

        let partial_order = super::IncompleteOrder {
            equal_boundaries: Vec::from([(
                Rc::new(IntervalBoundary::new_bound(
                    WeightedSum::new([(Parameter::new("n"), 1)]),
                    0,
                )),
                vec![Rc::new(IntervalBoundary::new_bound(
                    WeightedSum::new([(Parameter::new("f"), 1)]),
                    0,
                ))],
            )]),
            single_variable_order: HashMap::from([(
                Variable::new("x"),
                vec![
                    Rc::new(IntervalBoundary::from_const(0)),
                    Rc::new(IntervalBoundary::from_const(1)),
                ],
            )]),
            multi_variable_order: HashMap::new(),
        };

        assert!(partial_order.check_satisfiable(&mut ctx));

        let partial_order = super::IncompleteOrder {
            equal_boundaries: Vec::from([(
                Rc::new(IntervalBoundary::new_bound(
                    WeightedSum::new([(Parameter::new("n"), 1)]),
                    0,
                )),
                vec![Rc::new(IntervalBoundary::new_bound(
                    WeightedSum::new([(Parameter::new("f"), 1)]),
                    0,
                ))],
            )]),
            single_variable_order: HashMap::from([(
                Variable::new("x"),
                vec![
                    Rc::new(IntervalBoundary::from_const(1)),
                    Rc::new(IntervalBoundary::from_const(0)),
                ],
            )]),
            multi_variable_order: HashMap::new(),
        };

        assert!(!partial_order.check_satisfiable(&mut ctx));
    }

    #[test]
    fn test_build_order() {
        let builder = SMTSolverBuilder::default();

        let rc = [BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Param(Parameter::new("n"))),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Const(3)),
        )];

        let ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_locations(vec![Location::new("l1"), Location::new("l2")])
            .unwrap()
            .with_parameters(vec![Parameter::new("n"), Parameter::new("f")])
            .unwrap()
            .initialize()
            .with_resilience_conditions(rc)
            .unwrap()
            .build();

        let mut ctx = StaticSMTContext::new(
            builder.clone(),
            ta.parameters().cloned(),
            Vec::new(),
            Vec::new(),
        )
        .unwrap();
        let rc = ta
            .resilience_conditions()
            .map(|rc| rc.encode_to_smt_with_ctx(ctx.get_smt_solver(), &ctx))
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let rc = ctx.get_smt_solver().and_many(rc);
        ctx.get_smt_solver_mut().assert(rc).unwrap();

        let partial_order = super::IncompleteOrder {
            equal_boundaries: Vec::from([(
                Rc::new(IntervalBoundary::new_bound(
                    WeightedSum::new([(Parameter::new("n"), 1)]),
                    0,
                )),
                vec![Rc::new(IntervalBoundary::new_bound(
                    WeightedSum::new([(Parameter::new("f"), 1)]),
                    0,
                ))],
            )]),
            single_variable_order: HashMap::from([(
                Variable::new("x"),
                vec![
                    Rc::new(IntervalBoundary::from_const(0)),
                    Rc::new(IntervalBoundary::from_const(1)),
                    Rc::new(IntervalBoundary::from_const(2)),
                    Rc::new(IntervalBoundary::from_const(3)),
                ],
            )]),
            multi_variable_order: HashMap::new(),
        };

        let order_generator = SimpleOrderGeneratorContext {
            solver: ctx,
            incomplete_orders: vec![partial_order],
        };

        let order = order_generator.build_orders(&[Variable::new("x"), Variable::new("y")]);

        let expected_order = StaticIntervalOrder::new(
            HashMap::from([
                (
                    Variable::new("x"),
                    vec![
                        Interval::new(
                            IntervalBoundary::from_const(0),
                            false,
                            IntervalBoundary::from_const(1),
                            true,
                        ),
                        Interval::new(
                            IntervalBoundary::from_const(1),
                            false,
                            IntervalBoundary::from_const(2),
                            true,
                        ),
                        Interval::new(
                            IntervalBoundary::from_const(2),
                            false,
                            IntervalBoundary::from_const(3),
                            true,
                        ),
                        Interval::new(
                            IntervalBoundary::from_const(3),
                            false,
                            IntervalBoundary::new_infty(),
                            true,
                        ),
                    ],
                ),
                (
                    Variable::new("y"),
                    vec![
                        Interval::new(
                            IntervalBoundary::from_const(0),
                            false,
                            IntervalBoundary::from_const(1),
                            true,
                        ),
                        Interval::new(
                            IntervalBoundary::from_const(1),
                            false,
                            IntervalBoundary::new_infty(),
                            true,
                        ),
                    ],
                ),
            ]),
            HashMap::new(),
            HashMap::from([(
                IntervalBoundary::new_bound(WeightedSum::new([(Parameter::new("f"), 1)]), 0),
                IntervalBoundary::new_bound(WeightedSum::new([(Parameter::new("n"), 1)]), 0),
            )]),
        );

        assert_eq!(order.len(), 1);
        assert_eq!(
            order[0], expected_order,
            "Got: {}\n\nExpected: {}",
            order[0], expected_order
        );
    }

    #[test]
    fn test_add_interval_boundary_single_var() {
        let builder = SMTSolverBuilder::default();

        let rc = [
            BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Param(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(3)),
            ),
            BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Param(Parameter::new("f"))),
                ComparisonOp::Geq,
                Box::new(IntegerExpression::Const(0)),
            ),
        ];

        let ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_locations(vec![Location::new("l1"), Location::new("l2")])
            .unwrap()
            .with_parameters(vec![Parameter::new("n"), Parameter::new("f")])
            .unwrap()
            .initialize()
            .with_resilience_conditions(rc)
            .unwrap()
            .build();

        let order_generator = SimpleOrderGeneratorContext::new(&ta, builder.clone());

        // n
        let ib = IntervalBoundary::new_bound(
            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
            0,
        );

        let order_generator = order_generator
            .extend_order_with_interval_for_single_variable(&Variable::new("x"), &ib);

        let orders = order_generator.build_orders(&Vec::new());

        let expected_static_order = StaticIntervalOrder {
            equal_boundaries: HashMap::new(),
            single_var_order: HashMap::from([(
                Variable::new("x"),
                vec![
                    Interval::new_constant(0, 1),
                    Interval::new(
                        IntervalBoundary::from_const(1),
                        false,
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            0,
                        ),
                        true,
                    ),
                    Interval::new(
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            0,
                        ),
                        false,
                        IntervalBoundary::new_infty(),
                        true,
                    ),
                ],
            )]),
            multi_var_order: HashMap::new(),
        };

        assert_eq!(orders.len(), 1);
        assert_eq!(orders[0], expected_static_order);
    }

    #[test]
    fn test_add_interval_boundary_second_var_strictly_gt() {
        let builder = SMTSolverBuilder::default();

        let rc = [
            BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Param(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(3)),
            ),
            BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Param(Parameter::new("f"))),
                ComparisonOp::Geq,
                Box::new(IntegerExpression::Const(0)),
            ),
        ];

        let ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_locations(vec![Location::new("l1"), Location::new("l2")])
            .unwrap()
            .with_parameters(vec![Parameter::new("n"), Parameter::new("f")])
            .unwrap()
            .initialize()
            .with_resilience_conditions(rc)
            .unwrap()
            .build();

        let mut ctx = StaticSMTContext::new(
            builder.clone(),
            ta.parameters().cloned(),
            Vec::new(),
            Vec::new(),
        )
        .unwrap();
        let rc = ta
            .resilience_conditions()
            .map(|rc| rc.encode_to_smt_with_ctx(ctx.get_smt_solver(), &ctx))
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let rc = ctx.get_smt_solver().and_many(rc);
        ctx.get_smt_solver_mut().assert(rc).unwrap();

        let partial_order = IncompleteOrder {
            equal_boundaries: Vec::new(),
            single_variable_order: HashMap::from([(
                Variable::new("x"),
                vec![
                    Rc::new(IntervalBoundary::from_const(Fraction::from(0))),
                    Rc::new(IntervalBoundary::from_const(Fraction::from(1))),
                    Rc::new(IntervalBoundary::new_bound(
                        WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                        0,
                    )),
                ],
            )]),
            multi_variable_order: HashMap::new(),
        };

        let order_generator = SimpleOrderGeneratorContext {
            solver: ctx,
            incomplete_orders: vec![partial_order],
        };

        let ib = IntervalBoundary::new_bound(
            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
            2,
        );

        let orders = order_generator
            .extend_order_with_interval_for_single_variable(&Variable::new("x"), &ib)
            .build_orders(&Vec::new());

        let expected_static_order = StaticIntervalOrder {
            equal_boundaries: HashMap::new(),
            single_var_order: HashMap::from([(
                Variable::new("x"),
                vec![
                    Interval::new_constant(0, 1),
                    Interval::new(
                        IntervalBoundary::from_const(1),
                        false,
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            0,
                        ),
                        true,
                    ),
                    Interval::new(
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            0,
                        ),
                        false,
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            2,
                        ),
                        true,
                    ),
                    Interval::new(
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            2,
                        ),
                        false,
                        IntervalBoundary::new_infty(),
                        true,
                    ),
                ],
            )]),
            multi_var_order: HashMap::new(),
        };

        assert_eq!(orders.len(), 1);
        assert_eq!(orders[0], expected_static_order);
    }

    #[test]
    fn test_add_interval_boundary_add_ib_twice() {
        let builder = SMTSolverBuilder::default();

        let rc = [
            BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Param(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(3)),
            ),
            BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Param(Parameter::new("f"))),
                ComparisonOp::Geq,
                Box::new(IntegerExpression::Const(0)),
            ),
        ];

        let ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_locations(vec![Location::new("l1"), Location::new("l2")])
            .unwrap()
            .with_parameters(vec![Parameter::new("n"), Parameter::new("f")])
            .unwrap()
            .initialize()
            .with_resilience_conditions(rc)
            .unwrap()
            .build();

        let mut ctx = StaticSMTContext::new(
            builder.clone(),
            ta.parameters().cloned(),
            Vec::new(),
            Vec::new(),
        )
        .unwrap();
        let rc = ta
            .resilience_conditions()
            .map(|rc| rc.encode_to_smt_with_ctx(ctx.get_smt_solver(), &ctx))
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let rc = ctx.get_smt_solver().and_many(rc);
        ctx.get_smt_solver_mut().assert(rc).unwrap();

        let partial_order = IncompleteOrder {
            equal_boundaries: Vec::new(),
            single_variable_order: HashMap::from([(
                Variable::new("x"),
                vec![
                    Rc::new(IntervalBoundary::from_const(Fraction::from(0))),
                    Rc::new(IntervalBoundary::from_const(Fraction::from(1))),
                    Rc::new(IntervalBoundary::new_bound(
                        WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                        0,
                    )),
                    Rc::new(IntervalBoundary::new_bound(
                        WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                        2,
                    )),
                ],
            )]),
            multi_variable_order: HashMap::new(),
        };

        let order_generator = SimpleOrderGeneratorContext {
            solver: ctx,
            incomplete_orders: vec![partial_order],
        };

        let ib = IntervalBoundary::new_bound(
            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
            2,
        );

        let orders = order_generator
            .extend_order_with_interval_for_single_variable(&Variable::new("x"), &ib)
            .build_orders(&Vec::new());

        let expected_static_order = StaticIntervalOrder {
            equal_boundaries: HashMap::new(),
            single_var_order: HashMap::from([(
                Variable::new("x"),
                vec![
                    Interval::new_constant(0, 1),
                    Interval::new(
                        IntervalBoundary::from_const(1),
                        false,
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            0,
                        ),
                        true,
                    ),
                    Interval::new(
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            0,
                        ),
                        false,
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            2,
                        ),
                        true,
                    ),
                    Interval::new(
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            2,
                        ),
                        false,
                        IntervalBoundary::new_infty(),
                        true,
                    ),
                ],
            )]),
            multi_var_order: HashMap::new(),
        };

        assert_eq!(orders.len(), 1);
        assert_eq!(orders[0], expected_static_order);
    }

    #[test]
    fn test_add_interval_boundary_add_ib_twice_eq() {
        let builder = SMTSolverBuilder::default();

        let rc = [
            BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Param(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(3)),
            ),
            BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Param(Parameter::new("f"))),
                ComparisonOp::Geq,
                Box::new(IntegerExpression::Const(0)),
            ),
        ];

        let ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_locations(vec![Location::new("l1"), Location::new("l2")])
            .unwrap()
            .with_parameters(vec![Parameter::new("n"), Parameter::new("f")])
            .unwrap()
            .initialize()
            .with_resilience_conditions(rc)
            .unwrap()
            .build();

        let order_generator = SimpleOrderGeneratorContext::new(&ta, builder.clone());

        let order_generator = order_generator
            .extend_order_with_interval_for_single_variable(
                &Variable::new("x"),
                &IntervalBoundary::new_bound(
                    WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                    0,
                ),
            )
            .extend_order_with_interval_for_single_variable(
                &Variable::new("x"),
                &IntervalBoundary::new_bound(
                    WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                    0,
                ),
            );

        let ib = IntervalBoundary::new_bound(
            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
            2,
        );

        let orders = order_generator
            .extend_order_with_interval_for_single_variable(&Variable::new("x"), &ib)
            .build_orders(&Vec::new());

        let expected_static_order = StaticIntervalOrder {
            equal_boundaries: HashMap::new(),
            single_var_order: HashMap::from([(
                Variable::new("x"),
                vec![
                    Interval::new_constant(0, 1),
                    Interval::new(
                        IntervalBoundary::from_const(1),
                        false,
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            0,
                        ),
                        true,
                    ),
                    Interval::new(
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            0,
                        ),
                        false,
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            2,
                        ),
                        true,
                    ),
                    Interval::new(
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            2,
                        ),
                        false,
                        IntervalBoundary::new_infty(),
                        true,
                    ),
                ],
            )]),
            multi_var_order: HashMap::new(),
        };

        assert_eq!(orders.len(), 1);
        assert_eq!(
            orders[0], expected_static_order,
            "Expected:\n{}\n\nGot:\n{}\n\n",
            expected_static_order, orders[0]
        );
    }

    #[test]
    fn test_add_interval_boundary_add_ib_new_param() {
        let builder = SMTSolverBuilder::default();

        let rc = [
            BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Param(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(3)),
            ),
            BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Param(Parameter::new("f"))),
                ComparisonOp::Geq,
                Box::new(IntegerExpression::Const(0)),
            ),
        ];

        let ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_locations(vec![Location::new("l1"), Location::new("l2")])
            .unwrap()
            .with_parameters(vec![Parameter::new("n"), Parameter::new("f")])
            .unwrap()
            .initialize()
            .with_resilience_conditions(rc)
            .unwrap()
            .build();

        let order_generator = SimpleOrderGeneratorContext::new(&ta, builder.clone());

        let order_generator = order_generator
            .extend_order_with_interval_for_single_variable(
                &Variable::new("x"),
                &IntervalBoundary::new_bound(
                    WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                    0,
                ),
            )
            .extend_order_with_interval_for_single_variable(
                &Variable::new("x"),
                &IntervalBoundary::new_bound(
                    WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                    2,
                ),
            );

        // f + 1
        let ib = Rc::new(IntervalBoundary::new_bound(
            WeightedSum::new([(Parameter::new("f"), Fraction::from(1))]),
            1,
        ));

        let orders = order_generator
            .extend_order_with_interval_for_single_variable(&Variable::new("x"), &ib)
            .build_orders(&Vec::new());

        assert_eq!(orders.len(), 6);

        let expected_static_order1 = StaticIntervalOrder {
            equal_boundaries: HashMap::from([(
                ib.as_ref().clone(),
                IntervalBoundary::from_const(1),
            )]),
            single_var_order: HashMap::from([(
                Variable::new("x"),
                vec![
                    Interval::new_constant(0, 1),
                    Interval::new(
                        IntervalBoundary::from_const(1),
                        false,
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            0,
                        ),
                        true,
                    ),
                    Interval::new(
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            0,
                        ),
                        false,
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            2,
                        ),
                        true,
                    ),
                    Interval::new(
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            2,
                        ),
                        false,
                        IntervalBoundary::new_infty(),
                        true,
                    ),
                ],
            )]),
            multi_var_order: HashMap::new(),
        };

        assert!(orders.contains(&expected_static_order1));

        let expected_static_order2 = StaticIntervalOrder {
            equal_boundaries: HashMap::from([(
                ib.as_ref().clone(),
                IntervalBoundary::new_bound(
                    WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                    0,
                ),
            )]),
            single_var_order: HashMap::from([(
                Variable::new("x"),
                vec![
                    Interval::new_constant(0, 1),
                    Interval::new(
                        IntervalBoundary::from_const(1),
                        false,
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            0,
                        ),
                        true,
                    ),
                    Interval::new(
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            0,
                        ),
                        false,
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            2,
                        ),
                        true,
                    ),
                    Interval::new(
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            2,
                        ),
                        false,
                        IntervalBoundary::new_infty(),
                        true,
                    ),
                ],
            )]),
            multi_var_order: HashMap::new(),
        };

        assert!(orders.contains(&expected_static_order2));

        let expected_static_order3 = StaticIntervalOrder {
            equal_boundaries: HashMap::from([(
                ib.as_ref().clone(),
                IntervalBoundary::new_bound(
                    WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                    2,
                ),
            )]),
            single_var_order: HashMap::from([(
                Variable::new("x"),
                vec![
                    Interval::new_constant(0, 1),
                    Interval::new(
                        IntervalBoundary::from_const(1),
                        false,
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            0,
                        ),
                        true,
                    ),
                    Interval::new(
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            0,
                        ),
                        false,
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            2,
                        ),
                        true,
                    ),
                    Interval::new(
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            2,
                        ),
                        false,
                        IntervalBoundary::new_infty(),
                        true,
                    ),
                ],
            )]),
            multi_var_order: HashMap::new(),
        };

        assert!(orders.contains(&expected_static_order3));

        let expected_static_order4 = StaticIntervalOrder {
            equal_boundaries: HashMap::new(),
            single_var_order: HashMap::from([(
                Variable::new("x"),
                vec![
                    Interval::new_constant(0, 1),
                    Interval::new(
                        IntervalBoundary::from_const(1),
                        false,
                        ib.as_ref().clone(),
                        true,
                    ),
                    Interval::new(
                        ib.as_ref().clone(),
                        false,
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            0,
                        ),
                        true,
                    ),
                    Interval::new(
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            0,
                        ),
                        false,
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            2,
                        ),
                        true,
                    ),
                    Interval::new(
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            2,
                        ),
                        false,
                        IntervalBoundary::new_infty(),
                        true,
                    ),
                ],
            )]),
            multi_var_order: HashMap::new(),
        };

        assert!(orders.contains(&expected_static_order4));

        let expected_static_order5 = StaticIntervalOrder {
            equal_boundaries: HashMap::new(),
            single_var_order: HashMap::from([(
                Variable::new("x"),
                vec![
                    Interval::new_constant(0, 1),
                    Interval::new(
                        IntervalBoundary::from_const(1),
                        false,
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            0,
                        ),
                        true,
                    ),
                    Interval::new(
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            0,
                        ),
                        false,
                        ib.as_ref().clone(),
                        true,
                    ),
                    Interval::new(
                        ib.as_ref().clone(),
                        false,
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            2,
                        ),
                        true,
                    ),
                    Interval::new(
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            2,
                        ),
                        false,
                        IntervalBoundary::new_infty(),
                        true,
                    ),
                ],
            )]),
            multi_var_order: HashMap::new(),
        };
        assert!(orders.contains(&expected_static_order5));

        let expected_static_order6 = StaticIntervalOrder {
            equal_boundaries: HashMap::new(),
            single_var_order: HashMap::from([(
                Variable::new("x"),
                vec![
                    Interval::new_constant(0, 1),
                    Interval::new(
                        IntervalBoundary::from_const(1),
                        false,
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            0,
                        ),
                        true,
                    ),
                    Interval::new(
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            0,
                        ),
                        false,
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            2,
                        ),
                        true,
                    ),
                    Interval::new(
                        IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            2,
                        ),
                        false,
                        ib.as_ref().clone(),
                        true,
                    ),
                    Interval::new(
                        ib.as_ref().clone(),
                        false,
                        IntervalBoundary::new_infty(),
                        true,
                    ),
                ],
            )]),
            multi_var_order: HashMap::new(),
        };

        assert!(orders.contains(&expected_static_order6));
    }

    #[test]
    fn test_display_incomplete_order() {
        let partial_order = IncompleteOrder {
            equal_boundaries: vec![
                (
                    Rc::new(IntervalBoundary::new_bound(
                        WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                        0,
                    )),
                    vec![Rc::new(IntervalBoundary::new_bound(
                        WeightedSum::new([(Parameter::new("f"), Fraction::from(1))]),
                        0,
                    ))],
                ),
                (
                    Rc::new(IntervalBoundary::new_bound(
                        WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                        1,
                    )),
                    vec![Rc::new(IntervalBoundary::new_bound(
                        WeightedSum::new([(Parameter::new("t"), Fraction::from(1))]),
                        0,
                    ))],
                ),
            ],
            single_variable_order: HashMap::from([
                (
                    Variable::new("x"),
                    vec![
                        Rc::new(IntervalBoundary::from_const(Fraction::from(0))),
                        Rc::new(IntervalBoundary::from_const(Fraction::from(1))),
                        Rc::new(IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            0,
                        )),
                        Rc::new(IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            2,
                        )),
                    ],
                ),
                (
                    Variable::new("y"),
                    vec![
                        Rc::new(IntervalBoundary::from_const(Fraction::from(0))),
                        Rc::new(IntervalBoundary::from_const(Fraction::from(1))),
                        Rc::new(IntervalBoundary::new_bound(
                            WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                            0,
                        )),
                    ],
                ),
            ]),
            multi_variable_order: HashMap::from([(
                WeightedSum::new([(Variable::new("x"), 1), (Variable::new("y"), 1)]),
                vec![
                    Rc::new(IntervalBoundary::from_const(Fraction::from(0))),
                    Rc::new(IntervalBoundary::from_const(Fraction::from(1))),
                ],
            )]),
        };

        let expected_display = "PartialOrder {\n    n == f && n + 1 == t,\n    x: 0 < 1 < n < n + 2,\n    y: 0 < 1 < n,\n    x + y: 0 < 1,\n}\n";
        assert_eq!(format!("{partial_order}"), expected_display);
    }
}
