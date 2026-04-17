//! This module implements a static order on intervals
//!
//! A static order on intervals is a fixed order on intervals, which defines
//! which interval borders are equal and the relative order among interval
//! borders.
//!

use core::fmt;
use std::collections::HashMap;

use taco_display_utils::join_iterator;

use simple_order_generator::SimpleOrderGeneratorContext;
use taco_smt_encoder::SMTSolverBuilder;
use taco_threshold_automaton::{
    ThresholdAutomaton,
    expressions::{Atomic, BooleanExpression, ComparisonOp, Variable},
    lia_threshold_automaton::integer_thresholds::{
        IntoNoDivBooleanExpr, ThresholdCompOp, ThresholdConstraint, WeightedSum,
    },
};

use crate::{
    HasAssociatedIntervals,
    interval::{Interval, IntervalBoundary, IntervalOrder, IntervalOrderError, IntervalOrderFor},
};

mod simple_order_generator;

/// Types implementing this trait define a static order on intervals that
/// associates every interval with an index for each variable
trait DefinesStaticIntervalOrder<T>: fmt::Display + IntervalOrder
where
    T: HasAssociatedIntervals,
{
    fn get_intervals<'a>(&'a self, var: &T) -> Result<&'a Vec<Interval>, IntervalOrderError<T>>;

    fn get_interval_index(&self, var: &T, i: &Interval) -> Result<usize, IntervalOrderError<T>>;

    fn get_interval_by_index<'a>(
        &'a self,
        var: &T,
        idx: usize,
    ) -> Result<&'a Interval, IntervalOrderError<T>>;

    /// Check whether the interval order replaces the interval boundary
    ///
    /// This method checks if the interval boundary `ib` is replaced by the
    /// interval order. If the interval boundary is replaced, the method returns
    /// the new interval boundary that replaces `ib`. If the interval boundary
    /// is not replaced, the method returns the original interval boundary.
    ///
    /// An interval might have been replaced if the interval boundary is
    /// considered equal to another boundary in the order.
    fn check_interval_replaced_by_eq(&self, ib: IntervalBoundary) -> IntervalBoundary;
}

/// Static order on intervals implementing `IntervalOrder` for variables and
/// sums of variables
#[derive(Debug, Clone, PartialEq)]
pub struct StaticIntervalOrder {
    /// Order on intervals for each variable
    single_var_order: HashMap<Variable, Vec<Interval>>,
    /// Order on intervals multi-variable guards
    multi_var_order: HashMap<WeightedSum<Variable>, Vec<Interval>>,
    /// Interval boundaries that are considered equal
    equal_boundaries: HashMap<IntervalBoundary, IntervalBoundary>,
}
impl StaticIntervalOrder {
    /// returns the underlying single_var_order
    pub fn single_var_order(&self) -> &HashMap<Variable, Vec<Interval>> {
        &self.single_var_order
    }
}

#[cfg(test)]
impl StaticIntervalOrder {
    /// Get a new empty order for test purposes
    pub fn new(
        single_var_order: HashMap<Variable, Vec<Interval>>,
        multi_var_order: HashMap<WeightedSum<Variable>, Vec<Interval>>,
        equal_boundaries: HashMap<IntervalBoundary, IntervalBoundary>,
    ) -> StaticIntervalOrder {
        StaticIntervalOrder {
            single_var_order,
            multi_var_order,
            equal_boundaries,
        }
    }
}

impl DefinesStaticIntervalOrder<Variable> for StaticIntervalOrder {
    fn get_intervals<'a>(
        &'a self,
        var: &Variable,
    ) -> Result<&'a Vec<Interval>, IntervalOrderError<Variable>> {
        let intervals = self
            .single_var_order
            .get(var)
            .ok_or_else(|| IntervalOrderError::VariableNotFound { var: var.clone() })?;
        Ok(intervals)
    }

    fn get_interval_index(
        &self,
        var: &Variable,
        i: &Interval,
    ) -> Result<usize, IntervalOrderError<Variable>> {
        let intervals = self.get_intervals(var)?;

        intervals.iter().position(|x| *x == *i).ok_or_else(|| {
            IntervalOrderError::IntervalNotFound {
                var: var.clone(),
                interval: i.clone(),
            }
        })
    }

    fn get_interval_by_index<'a>(
        &'a self,
        var: &Variable,
        mut idx: usize,
    ) -> Result<&'a Interval, IntervalOrderError<Variable>> {
        let intervals = self.get_intervals(var)?;

        if idx >= intervals.len() {
            idx = intervals.len() - 1;
        }

        Ok(&intervals[idx])
    }

    /// This function checks whether the interval needs to be replaced by
    /// another one because it is considered equal to another boundary in the
    /// order.
    ///
    /// This function must be called when converting thresholds in the order.
    fn check_interval_replaced_by_eq(&self, ib: IntervalBoundary) -> IntervalBoundary {
        if let Some(ib) = self.equal_boundaries.get(&ib) {
            return ib.clone();
        }

        ib
    }
}

impl DefinesStaticIntervalOrder<WeightedSum<Variable>> for StaticIntervalOrder {
    fn get_intervals<'a>(
        &'a self,
        var: &WeightedSum<Variable>,
    ) -> Result<&'a Vec<Interval>, IntervalOrderError<WeightedSum<Variable>>> {
        let intervals = self
            .multi_var_order
            .get(var)
            .ok_or_else(|| IntervalOrderError::VariableNotFound { var: var.clone() })?;

        Ok(intervals)
    }

    fn get_interval_index(
        &self,
        var: &WeightedSum<Variable>,
        i: &Interval,
    ) -> Result<usize, IntervalOrderError<WeightedSum<Variable>>> {
        let intervals = self.get_intervals(var)?;

        intervals.iter().position(|x| *x == *i).ok_or_else(|| {
            IntervalOrderError::IntervalNotFound {
                var: var.clone(),
                interval: i.clone(),
            }
        })
    }

    fn get_interval_by_index<'a>(
        &'a self,
        var: &WeightedSum<Variable>,
        mut idx: usize,
    ) -> Result<&'a Interval, IntervalOrderError<WeightedSum<Variable>>> {
        let intervals = self.get_intervals(var)?;

        if intervals.is_empty() {
            unreachable!("Should at least contain one interval!");
        }
        if idx >= intervals.len() {
            idx = intervals.len() - 1;
        }

        Ok(&intervals[idx])
    }

    fn check_interval_replaced_by_eq(&self, ib: IntervalBoundary) -> IntervalBoundary {
        if let Some(ib) = self.equal_boundaries.get(&ib) {
            return ib.clone();
        }

        ib
    }
}

impl<T: HasAssociatedIntervals, U: DefinesStaticIntervalOrder<T>> IntervalOrderFor<T> for U {
    fn get_number_of_intervals(&self, var: &T) -> Result<usize, IntervalOrderError<T>> {
        Ok(self.get_intervals(var)?.len())
    }

    fn lt(&self, var: &T, i1: &Interval, i2: &Interval) -> Result<bool, IntervalOrderError<T>> {
        let idx1 = self.get_interval_index(var, i1)?;
        let idx2 = self.get_interval_index(var, i2)?;

        Ok(idx1 < idx2)
    }

    fn gt(&self, var: &T, i1: &Interval, i2: &Interval) -> Result<bool, IntervalOrderError<T>> {
        let idx1 = self.get_interval_index(var, i1)?;
        let idx2 = self.get_interval_index(var, i2)?;

        Ok(idx1 > idx2)
    }

    fn get_next_interval<'a>(
        &'a self,
        var: &T,
        i: &Interval,
    ) -> Result<Option<&'a Interval>, IntervalOrderError<T>> {
        let idx = self.get_interval_index(var, i)?;

        if idx >= self.get_number_of_intervals(var)? - 1 {
            return Ok(None);
        }

        Ok(Some(self.get_interval_by_index(var, idx + 1)?))
    }

    fn get_previous_interval<'a>(
        &'a self,
        var: &T,
        i: &Interval,
    ) -> Result<Option<&'a Interval>, IntervalOrderError<T>> {
        let idx = self.get_interval_index(var, i)?;

        if idx == 0 {
            return Ok(None);
        }

        Ok(Some(self.get_interval_by_index(var, idx - 1)?))
    }

    fn compute_enabled_intervals_of_threshold(
        &self,
        t: &T,
        thr: &ThresholdConstraint,
    ) -> Result<Vec<Interval>, IntervalOrderError<T>> {
        let lb = IntervalBoundary::from_threshold_constraint(thr);

        let lb: IntervalBoundary = self.check_interval_replaced_by_eq(lb);

        let intervals = self.get_intervals(t)?;

        let (idx, _) = intervals
            .iter()
            .enumerate()
            .find(|(_index, i)| i.check_is_contained(&lb))
            .ok_or_else(|| IntervalOrderError::ThresholdExtractionError {
                var: t.clone(),
                thr: thr.clone(),
            })?;

        let result = match thr.get_op() {
            ThresholdCompOp::Geq => intervals[idx..].to_vec(),
            ThresholdCompOp::Lt => intervals[..idx].to_vec(),
        };

        Ok(result)
    }

    fn get_zero_interval(&self, t: &T) -> Result<&Interval, IntervalOrderError<T>> {
        Ok(self.get_intervals(t)?.first().unwrap())
    }

    fn get_all_intervals_of_t(&self, t: &T) -> Result<&Vec<Interval>, IntervalOrderError<T>> {
        self.get_intervals(t)
    }

    fn check_interval_replaced(&self, ib: IntervalBoundary) -> IntervalBoundary {
        self.check_interval_replaced_by_eq(ib)
    }
}

impl IntervalOrder for StaticIntervalOrder {
    fn order_to_boolean_expr<T: Atomic>(&self) -> Vec<BooleanExpression<T>> {
        let eq_constr = self.equal_boundaries.iter().map(|(ib_1, ib_2)| {
            let ib_1 = ib_1.get_threshold().expect("Infinite interval in order");
            let ib_2 = ib_2.get_threshold().expect("Infinite interval in order");

            ib_1.encode_comparison_to_boolean_expression(ComparisonOp::Eq, ib_2)
        });

        let single_var_constr = self.single_var_order.values().flat_map(|intervals| {
            intervals
                .iter()
                .filter(|i| i.ub() != &IntervalBoundary::Infty)
                .map(|interval| {
                    if interval.lb() == &IntervalBoundary::Infty {
                        debug_assert!(false, "Interval with lower bound ∞ found");
                        return BooleanExpression::False;
                    }

                    let lb = interval
                        .lb()
                        .get_threshold()
                        .expect("Infinite interval in order");
                    let ub = interval
                        .ub()
                        .get_threshold()
                        .expect("Infinite interval in order");

                    lb.encode_comparison_to_boolean_expression(ComparisonOp::Lt, ub)
                })
        });

        let multi_var_constr = self.multi_var_order.values().flat_map(|intervals| {
            intervals
                .iter()
                .filter(|i| i.ub() != &IntervalBoundary::Infty)
                .map(|interval| {
                    if interval.lb() == &IntervalBoundary::Infty {
                        debug_assert!(false, "Interval with lower bound ∞ found");
                        return BooleanExpression::False;
                    }

                    let lb = interval
                        .lb()
                        .get_threshold()
                        .expect("Infinite interval in order");
                    let ub = interval
                        .ub()
                        .get_threshold()
                        .expect("Infinite interval in order");

                    lb.encode_comparison_to_boolean_expression(ComparisonOp::Lt, ub)
                })
        });

        eq_constr
            .chain(single_var_constr)
            .chain(multi_var_constr)
            .collect()
    }
}

impl fmt::Display for StaticIntervalOrder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "intervalOrder {{")?;

        if !self.equal_boundaries.is_empty() {
            writeln!(
                f,
                "    {};",
                join_iterator(
                    self.equal_boundaries
                        .iter()
                        .map(|(ib1, ib2)| format!("{ib1} == {ib2}")),
                    " && "
                )
            )?;
        }

        if !self.single_var_order.is_empty() {
            let mut sorted_single_var = self.single_var_order.iter().collect::<Vec<_>>();
            sorted_single_var.sort_by_key(|(a, _)| *a);

            for (var, intervals) in sorted_single_var {
                writeln!(f, "    {}: {};", var, join_iterator(intervals.iter(), ", "))?;
            }
        }

        if !self.multi_var_order.is_empty() {
            for (var, intervals) in &self.multi_var_order {
                writeln!(f, "    {}: {};", var, join_iterator(intervals.iter(), ", "))?;
            }
        }

        write!(f, "}}")
    }
}

/// Builder for generating static interval orders
pub struct StaticIntervalOrderBuilder {
    order_generator: SimpleOrderGeneratorContext,
    vars: Vec<Variable>,
}

impl StaticIntervalOrderBuilder {
    /// Create a new static interval order builder
    pub fn new<T: ThresholdAutomaton>(ta: &T, smt_solver_builder: SMTSolverBuilder) -> Self {
        let orders = SimpleOrderGeneratorContext::new(ta, smt_solver_builder);
        let vars = ta.variables().cloned().collect::<Vec<_>>();

        StaticIntervalOrderBuilder {
            order_generator: orders,
            vars,
        }
    }

    /// Add an interval found for a single variable
    pub fn add_single_variable_interval(self, var: &Variable, interval: &IntervalBoundary) -> Self {
        let orders = self
            .order_generator
            .extend_order_with_interval_for_single_variable(var, interval);

        StaticIntervalOrderBuilder {
            order_generator: orders,
            vars: self.vars,
        }
    }

    /// Add an interval found for a sum of variables
    pub fn add_multi_variable_interval(
        self,
        sum: &WeightedSum<Variable>,
        interval: &IntervalBoundary,
    ) -> Self {
        let orders = self
            .order_generator
            .extend_order_with_interval_for_multi_variable(sum, interval);

        StaticIntervalOrderBuilder {
            order_generator: orders,
            vars: self.vars,
        }
    }

    /// Generate all possible orders on intervals
    pub fn build(self) -> Vec<StaticIntervalOrder> {
        self.order_generator.build_orders(&self.vars)
    }
}

#[cfg(test)]
mod tests {

    use std::collections::{BTreeMap, HashMap};

    use taco_threshold_automaton::expressions::fraction::Fraction;
    use taco_threshold_automaton::expressions::{
        BooleanExpression, ComparisonOp, IntegerExpression, Parameter,
    };

    use taco_threshold_automaton::expressions::Variable;
    use taco_threshold_automaton::lia_threshold_automaton::integer_thresholds::{
        Threshold, ThresholdCompOp, ThresholdConstraint, WeightedSum,
    };

    use crate::builder::static_interval_order::{DefinesStaticIntervalOrder, StaticIntervalOrder};
    use crate::interval::{
        Interval, IntervalBoundary, IntervalOrder, IntervalOrderError, IntervalOrderFor,
    };

    #[test]
    fn test_get_interval_index_single_var() {
        let var = Variable::new("x");
        let interval1 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 1)),
            false,
            IntervalBoundary::Infty,
            false,
        );

        let mut internal_order = HashMap::new();
        internal_order.insert(var.clone(), vec![interval1.clone()]);

        let order = StaticIntervalOrder {
            single_var_order: internal_order,
            multi_var_order: HashMap::new(),
            equal_boundaries: HashMap::new(),
        };

        assert_eq!(order.get_interval_index(&var, &interval1).unwrap(), 0);

        let interval2 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 2)),
            false,
            IntervalBoundary::Infty,
            true,
        );
        let err = order.get_interval_index(&var, &interval2);
        assert!(err.is_err());
        assert!(matches!(
            err.unwrap_err(),
            IntervalOrderError::IntervalNotFound { .. }
        ));
    }

    #[test]
    fn get_interval_index_multi_var() {
        let var1 = Variable::new("x");
        let var2 = Variable::new("y");
        let sum = WeightedSum::new(BTreeMap::from([(var1.clone(), 1), (var2.clone(), 1)]));
        let interval1 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 1)),
            false,
            IntervalBoundary::Infty,
            true,
        );

        let mut internal_order = HashMap::new();
        internal_order.insert(sum.clone(), vec![interval1.clone()]);

        let order = StaticIntervalOrder {
            single_var_order: HashMap::new(),
            multi_var_order: internal_order,
            equal_boundaries: HashMap::new(),
        };

        assert_eq!(order.get_interval_index(&sum, &interval1).unwrap(), 0);

        let interval2 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 2)),
            false,
            IntervalBoundary::Infty,
            true,
        );
        let err = order.get_interval_index(&sum, &interval2);
        assert!(err.is_err());
        assert!(matches!(
            err.unwrap_err(),
            IntervalOrderError::IntervalNotFound { .. }
        ));
    }

    #[test]
    fn test_get_interval_by_index_single_var() {
        let var = Variable::new("x");
        let interval1 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 1)),
            false,
            IntervalBoundary::Infty,
            true,
        );

        let mut internal_order = HashMap::new();
        internal_order.insert(var.clone(), vec![interval1.clone()]);

        let order = StaticIntervalOrder {
            single_var_order: internal_order,
            multi_var_order: HashMap::new(),
            equal_boundaries: HashMap::new(),
        };

        assert_eq!(order.get_interval_by_index(&var, 0).unwrap(), &interval1);
        assert_eq!(order.get_interval_by_index(&var, 1).unwrap(), &interval1);
    }

    #[test]
    fn get_interval_by_index_multi_var() {
        let var1 = Variable::new("x");
        let var2 = Variable::new("y");
        let sum = WeightedSum::new(BTreeMap::from([(var1.clone(), 1), (var2.clone(), 1)]));
        let interval1 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 1)),
            false,
            IntervalBoundary::Infty,
            true,
        );

        let mut internal_order = HashMap::new();
        internal_order.insert(sum.clone(), vec![interval1.clone()]);

        let order = StaticIntervalOrder {
            single_var_order: HashMap::new(),
            multi_var_order: internal_order,
            equal_boundaries: HashMap::new(),
        };

        assert_eq!(order.get_interval_by_index(&sum, 0).unwrap(), &interval1);
        assert_eq!(order.get_interval_by_index(&sum, 1).unwrap(), &interval1);
    }

    #[test]
    fn test_interval_order_lt() {
        let var = Variable::new("x");
        let interval1 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 1)),
            false,
            IntervalBoundary::Infty,
            true,
        );
        let interval2 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 2)),
            false,
            IntervalBoundary::Infty,
            true,
        );
        let mut internal_order = HashMap::new();
        internal_order.insert(var.clone(), vec![interval1.clone(), interval2.clone()]);
        let order = StaticIntervalOrder {
            single_var_order: internal_order,
            multi_var_order: HashMap::new(),
            equal_boundaries: HashMap::new(),
        };

        assert!(order.lt(&var, &interval1, &interval2).unwrap());
        assert!(!order.lt(&var, &interval2, &interval1).unwrap());
    }

    #[test]
    fn test_interval_order_gt() {
        let var = Variable::new("x");
        let interval1 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 1)),
            false,
            IntervalBoundary::Infty,
            true,
        );
        let interval2 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 2)),
            false,
            IntervalBoundary::Infty,
            true,
        );
        let mut internal_order = HashMap::new();
        internal_order.insert(var.clone(), vec![interval1.clone(), interval2.clone()]);
        let order = StaticIntervalOrder {
            single_var_order: internal_order,
            multi_var_order: HashMap::new(),
            equal_boundaries: HashMap::new(),
        };

        assert!(order.gt(&var, &interval2, &interval1).unwrap());
        assert!(!order.gt(&var, &interval1, &interval2).unwrap());
    }

    #[test]
    fn test_get_next_interval() {
        let var = Variable::new("x");
        let interval1 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 1)),
            false,
            IntervalBoundary::Infty,
            true,
        );
        let interval2 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 2)),
            false,
            IntervalBoundary::Infty,
            true,
        );
        let mut internal_order = HashMap::new();
        internal_order.insert(var.clone(), vec![interval1.clone(), interval2.clone()]);
        let order = StaticIntervalOrder {
            single_var_order: internal_order,
            multi_var_order: HashMap::new(),
            equal_boundaries: HashMap::new(),
        };

        assert_eq!(
            order.get_next_interval(&var, &interval1).unwrap(),
            Some(&interval2)
        );
        assert_eq!(order.get_next_interval(&var, &interval2).unwrap(), None);
    }

    #[test]
    fn test_get_previous_interval() {
        let var = Variable::new("x");
        let interval1 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 1)),
            false,
            IntervalBoundary::Infty,
            true,
        );
        let interval2 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 2)),
            false,
            IntervalBoundary::Infty,
            true,
        );
        let mut internal_order = HashMap::new();
        internal_order.insert(var.clone(), vec![interval1.clone(), interval2.clone()]);
        let order = StaticIntervalOrder {
            single_var_order: internal_order,
            multi_var_order: HashMap::new(),
            equal_boundaries: HashMap::new(),
        };

        assert_eq!(
            order.get_previous_interval(&var, &interval2).unwrap(),
            Some(&interval1)
        );
        assert_eq!(order.get_previous_interval(&var, &interval1).unwrap(), None);
    }

    #[test]
    fn test_get_number_of_intervals() {
        let var = Variable::new("x");
        let interval1 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 1)),
            false,
            IntervalBoundary::Infty,
            true,
        );
        let interval2 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 2)),
            false,
            IntervalBoundary::Infty,
            true,
        );
        let mut internal_order = HashMap::new();
        internal_order.insert(var.clone(), vec![interval1, interval2]);
        let order = StaticIntervalOrder {
            single_var_order: internal_order,
            multi_var_order: HashMap::new(),
            equal_boundaries: HashMap::new(),
        };

        assert_eq!(order.get_number_of_intervals(&var).unwrap(), 2);
    }

    #[test]
    fn test_empty_intervals() {
        let var = Variable::new("x");
        let mut internal_order = HashMap::new();
        internal_order.insert(var.clone(), vec![]);
        let order = StaticIntervalOrder {
            single_var_order: internal_order,
            multi_var_order: HashMap::new(),
            equal_boundaries: HashMap::new(),
        };

        assert_eq!(order.get_number_of_intervals(&var).unwrap(), 0);
    }

    #[test]
    fn test_variable_not_found() {
        let var = Variable::new("x");
        let order = StaticIntervalOrder {
            single_var_order: HashMap::new(),
            multi_var_order: HashMap::new(),
            equal_boundaries: HashMap::new(),
        };

        assert!(order.get_number_of_intervals(&var).is_err());
    }

    #[test]
    fn test_interval_order_with_multiple_variables() {
        let var1 = Variable::new("x");
        let var2 = Variable::new("y");
        let interval1 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 1)),
            false,
            IntervalBoundary::Infty,
            true,
        );
        let interval2 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 2)),
            false,
            IntervalBoundary::Infty,
            true,
        );

        let mut internal_order = HashMap::new();
        internal_order.insert(var1.clone(), vec![interval1.clone()]);
        internal_order.insert(var2.clone(), vec![interval2.clone()]);

        let order = StaticIntervalOrder {
            single_var_order: internal_order,
            multi_var_order: HashMap::new(),
            equal_boundaries: HashMap::new(),
        };

        assert_eq!(order.get_number_of_intervals(&var1).unwrap(), 1);
        assert_eq!(order.get_number_of_intervals(&var2).unwrap(), 1);
        assert!(
            order
                .get_next_interval(&var1, &interval1)
                .unwrap()
                .is_none()
        );
        assert!(
            order
                .get_next_interval(&var2, &interval2)
                .unwrap()
                .is_none()
        );
        assert!(
            order
                .get_previous_interval(&var1, &interval1)
                .unwrap()
                .is_none()
        );
        assert!(
            order
                .get_previous_interval(&var2, &interval2)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn test_get_intervals_of_threshold() {
        let var = Variable::new("x");
        let interval1 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 1)),
            false,
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 1)),
            false,
        );
        let interval2 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 2)),
            false,
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 2)),
            false,
        );
        let interval3 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 3)),
            false,
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 3)),
            false,
        );

        let mut internal_order = HashMap::new();
        internal_order.insert(
            var.clone(),
            vec![interval1.clone(), interval2.clone(), interval3.clone()],
        );

        let order = StaticIntervalOrder {
            single_var_order: internal_order,
            multi_var_order: HashMap::new(),
            equal_boundaries: HashMap::new(),
        };

        // Test GEQ threshold
        let threshold_geq =
            ThresholdConstraint::new(ThresholdCompOp::Geq, Vec::<(Parameter, Fraction)>::new(), 2);
        let intervals_geq = order
            .compute_enabled_intervals_of_threshold(&var, &threshold_geq)
            .unwrap();
        assert_eq!(intervals_geq.len(), 2);
        assert_eq!(intervals_geq, vec![interval2.clone(), interval3.clone()]);

        // Test LT threshold
        let threshold_lt =
            ThresholdConstraint::new(ThresholdCompOp::Lt, Vec::<(Parameter, Fraction)>::new(), 3);
        let intervals_lt = order
            .compute_enabled_intervals_of_threshold(&var, &threshold_lt)
            .unwrap();
        assert_eq!(intervals_lt.len(), 2);
        assert_eq!(intervals_lt, vec![interval1.clone(), interval2.clone()]);
    }

    #[test]
    fn test_get_intervals_of_threshold_err() {
        let var = Variable::new("x");
        let interval1 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 1)),
            false,
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 1)),
            false,
        );
        let interval2 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 2)),
            false,
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 2)),
            false,
        );
        let interval3 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 3)),
            false,
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 3)),
            false,
        );

        let mut internal_order = HashMap::new();
        internal_order.insert(
            var.clone(),
            vec![interval1.clone(), interval2.clone(), interval3.clone()],
        );

        let order = StaticIntervalOrder {
            single_var_order: internal_order,
            multi_var_order: HashMap::new(),
            equal_boundaries: HashMap::new(),
        };

        // Test threshold not found
        let threshold =
            ThresholdConstraint::new(ThresholdCompOp::Geq, Vec::<(Parameter, Fraction)>::new(), 4);
        let err = order.compute_enabled_intervals_of_threshold(&var, &threshold);
        assert!(err.is_err());
        assert!(matches!(
            err.unwrap_err(),
            IntervalOrderError::ThresholdExtractionError { .. }
        ));
    }

    #[test]
    fn test_get_zero_interval() {
        let var = Variable::new("x");
        let interval1 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 1)),
            false,
            IntervalBoundary::Infty,
            false,
        );
        let interval2 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 2)),
            false,
            IntervalBoundary::Infty,
            false,
        );
        let mut internal_order = HashMap::new();
        internal_order.insert(var.clone(), vec![interval1.clone(), interval2.clone()]);
        let order = StaticIntervalOrder {
            single_var_order: internal_order,
            multi_var_order: HashMap::new(),
            equal_boundaries: HashMap::new(),
        };

        assert_eq!(order.get_zero_interval(&var).unwrap(), &interval1);
    }

    #[test]
    fn test_order_to_boolean_expr() {
        let var = Variable::new("x");
        let interval1 = Interval::new(
            IntervalBoundary::from_const(1),
            false,
            IntervalBoundary::from_const(2),
            true,
        );
        let interval2 = Interval::new(
            IntervalBoundary::from_const(2),
            false,
            IntervalBoundary::Infty,
            true,
        );

        let ib1 = IntervalBoundary::new_bound(WeightedSum::new([(Parameter::new("n"), 1)]), 0);
        let ib2 = IntervalBoundary::new_bound(WeightedSum::new([(Parameter::new("n"), 2)]), 0);

        let mut internal_order = HashMap::new();
        internal_order.insert(var.clone(), vec![interval1.clone(), interval2.clone()]);
        let order = StaticIntervalOrder {
            single_var_order: HashMap::from([(
                var.clone(),
                vec![interval1.clone(), interval2.clone()],
            )]),
            multi_var_order: HashMap::new(),
            equal_boundaries: HashMap::from([(ib2, ib1)]),
        };

        let exprs = order.order_to_boolean_expr::<Parameter>();

        assert_eq!(exprs.len(), 2);

        let expected_expr_1 = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(1)),
            ComparisonOp::Lt,
            Box::new(IntegerExpression::Const(2)),
        );
        assert!(exprs.contains(&expected_expr_1));

        let expected_expr_2 = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(2) * IntegerExpression::Param(Parameter::new("n"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Param(Parameter::new("n"))),
        );
        assert!(exprs.contains(&expected_expr_2));
    }

    #[test]
    fn test_display_static_interval_order() {
        let var1 = Variable::new("x");
        let var2 = Variable::new("y");
        let sum = WeightedSum::new(BTreeMap::from([(var1.clone(), 1), (var2.clone(), 1)]));
        let interval1 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 1)),
            false,
            IntervalBoundary::Infty,
            false,
        );
        let interval2 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 2)),
            false,
            IntervalBoundary::Infty,
            false,
        );
        let ib = IntervalBoundary::Bound(Threshold::new(
            WeightedSum::new([(Parameter::new("n"), 1)]),
            0,
        ));

        let single_var_internal_order = HashMap::from([
            (var1.clone(), vec![interval1.clone()]),
            (var2.clone(), vec![interval2.clone()]),
        ]);

        let multi_var_internal_order = HashMap::from([(sum.clone(), vec![interval1.clone()])]);

        let order = StaticIntervalOrder {
            single_var_order: single_var_internal_order,
            multi_var_order: multi_var_internal_order,
            equal_boundaries: HashMap::from([(IntervalBoundary::from_const(1), ib)]),
        };

        let expected =
            "intervalOrder {\n    1 == n;\n    x: [1, ∞[;\n    y: [2, ∞[;\n    x + y: [1, ∞[;\n}";
        assert_eq!(format!("{order}"), expected);
    }
}
