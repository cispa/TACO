//! Module for implementing atomic proposition types for model checking of
//! threshold automata
//!
//! This module implements the basic specification types for parameterized model
//! checking of threshold automata, as well as some helper functions that are
//! useful when translating form a specification language.

use core::fmt;
use std::{
    borrow::Borrow,
    cmp::max,
    collections::{HashMap, HashSet},
};

use taco_display_utils::join_iterator;
use taco_smt_encoder::expression_encoding::{EncodeToSMT, SMTSolverError, SMTVariableContext};
use taco_threshold_automaton::{
    VariableConstraint,
    expressions::{And, BooleanConnective, Location, Or, Parameter, Variable, fraction::Fraction},
    impl_bitand, impl_bitor,
    lia_threshold_automaton::{
        ConstraintRewriteError, LIAVariableConstraint,
        integer_thresholds::{DeriveFromIntegerComp, ThresholdCompOp, ThresholdConstraint},
    },
};

use crate::{TASpecification, internal_spec::Disjunction};

/// Type representing an upwards closed set of configurations
///
/// This type represents an upwards closed set of configurations symbolically.
/// Therefore, it can be seen as disjunction over [UpwardsClosedClause]
/// (i.e., since the clauses build a disjunction, it can be seen as a formula in
/// DNF). Its purpose is to serve as the low-level characterization of an error
/// state when model checking.
///
/// To create a new [UpwardsClosedSet] use the `new` methods and combine them
/// using the [And] and [Or] implementations. For an [UpwardsClosedSet] they can
/// also be thought of as taking the intersection or the union.
#[derive(Debug, Clone, PartialEq)]
pub struct UpwardsClosedSet {
    /// Set of clauses treated as a disjunction over all clauses
    clauses: Disjunction<UpwardsClosedClause>,
}

impl UpwardsClosedSet {
    /// Create a new [UpwardsClosedSet] which is unconstrained, i.e., contains
    /// all possible configurations
    pub fn new_top() -> Self {
        Self {
            clauses: [UpwardsClosedClause::new_top()].into(),
        }
    }

    /// Check whether this set contains all possible configurations / is a
    /// tautology
    pub fn is_top(&self) -> bool {
        self.clauses.iter().any(|c| c.is_top())
    }

    /// Create a new [UpwardsClosedSet] that is not inhabited, i.e., it contains
    /// no configurations
    pub fn new_bot() -> Self {
        Self { clauses: [].into() }
    }

    /// Check whether the current set of constraints is unsatisfiable
    pub fn is_bot(&self) -> bool {
        self.clauses.is_empty()
    }

    /// Create new [UpwardsClosedSet] which contains all configurations
    /// satisfying given constrain
    pub fn new_var_constraint(var_constr: LIAVariableConstraint) -> Self {
        let apc = UpwardsClosedClause::new().with_variable_constraint(var_constr);

        Self::new_from_clause(apc)
    }

    /// Create a new [UpwardsClosedSet] which contains all configurations for
    /// which all locations given in `cover` are occupied by at least one
    /// process
    pub fn new_cover<L: Borrow<Location>, I: IntoIterator<Item = L>>(cover: I) -> Self {
        let apc = UpwardsClosedClause::new().with_locs_to_cover(cover);

        Self::new_from_clause(apc)
    }

    /// Create a new [UpwardsClosedSet] requiring each location in `cover` to
    /// contain at least the given number of processes
    pub fn new_cover_int<L: Borrow<Location>, I: IntoIterator<Item = (L, u32)>>(cover: I) -> Self {
        let apc = UpwardsClosedClause::new().with_lower_bounds(cover);

        Self::new_from_clause(apc)
    }

    /// Create a new [UpwardsClosedSet] requiring each location in `cover` to
    /// contain at least the given number of processes, and each location in
    /// `empty` to contain no processes
    pub fn new_reach<
        L: Borrow<Location>,
        I: IntoIterator<Item = (L, u32)>,
        II: IntoIterator<Item = L>,
    >(
        cover: I,
        empty: II,
    ) -> Self {
        let apc = UpwardsClosedClause::new()
            .with_lower_bounds(cover)
            .with_locs_to_empty(empty);

        Self::new_from_clause(apc)
    }

    /// Create a new [UpwardsClosedSet] from a single clause
    fn new_from_clause(clause: UpwardsClosedClause) -> Self {
        Self {
            clauses: [clause].into(),
        }
    }

    /// Check whether this constraint contains a reachability constraint
    ///
    /// A reachability constraint requires at least one location to be empty,
    /// this function checks whether any of the clauses (see
    /// [UpwardsClosedClause]) contains a reachability specification.
    pub fn contains_reachability_constraint(&self) -> bool {
        self.clauses
            .iter()
            .any(|a| a.contains_reachability_constraint())
    }

    /// Iterator over the individual upwards closed clauses
    pub fn upwards_closed_clauses(&self) -> impl Iterator<Item = &UpwardsClosedClause> {
        self.clauses.iter()
    }
}

impl TASpecification for UpwardsClosedSet {
    fn locs_appearing(&self) -> impl IntoIterator<Item = &Location> {
        self.clauses.iter().flat_map(|a| a.locs_appearing())
    }

    fn var_constraint(&self) -> impl IntoIterator<Item = &LIAVariableConstraint> {
        self.clauses.iter().flat_map(|a| a.var_constraint())
    }
}

impl DeriveFromIntegerComp<Location, UpwardsClosedSetExtractionError> for UpwardsClosedSet {
    fn form_ordered_constr(
        scaled_t: HashMap<Location, Fraction>,
        mut thr_constr: ThresholdConstraint,
    ) -> Result<Self, UpwardsClosedSetExtractionError> {
        if scaled_t.len() != 1 {
            return Err(
                UpwardsClosedSetExtractionError::LocationConstraintMultiLocation(Box::new((
                    scaled_t, thr_constr,
                ))),
            );
        }

        let (loc, scale) = scaled_t.into_iter().next().unwrap();
        if scale.is_zero() {
            unreachable!(
                "Invalid target constraint constructed containing only parameters (locations are multiplied by zero)."
            );
        }
        thr_constr.scale(scale.inverse());

        if !thr_constr.get_threshold().is_constant() {
            return Err(
                UpwardsClosedSetExtractionError::LocationConstraintWithParameters(Box::new((
                    loc, thr_constr,
                ))),
            );
        }
        let mut c = thr_constr.get_threshold().get_const().unwrap();

        match thr_constr.get_op() {
            ThresholdCompOp::Geq | ThresholdCompOp::Gt => {
                // For >: add one if ceil does not increase
                if ThresholdCompOp::Gt == thr_constr.get_op() && c.is_integer() {
                    c += Fraction::from(1);
                }

                if c.is_negative() || c.is_zero() {
                    return Ok(UpwardsClosedSet::new_top());
                }

                let c = c.get_ceil().unwrap();
                Ok(UpwardsClosedSet::new_from_clause(
                    UpwardsClosedClause::new().with_lower_bounds([(loc, c)]),
                ))
            }
            ThresholdCompOp::Lt | ThresholdCompOp::Leq => {
                // For <=: If the floor count does not
                if ThresholdCompOp::Leq == thr_constr.get_op() && c.is_integer() {
                    c += Fraction::from(1);
                }

                // Since we are treating integers, this constraint is equivalent
                // to \bot
                if c.is_zero() || c.is_negative() {
                    return Ok(UpwardsClosedSet::new_bot());
                }

                // < 1 --> Can be translated to 0
                if c.get_ceil() == Some(1) {
                    return Ok(UpwardsClosedSet::new_from_clause(
                        UpwardsClosedClause::new().with_locs_to_empty([loc]),
                    ));
                }

                Err(
                    UpwardsClosedSetExtractionError::LocationConstraintNotUpwardsClosed(Box::new(
                        (loc, thr_constr),
                    )),
                )
            }
        }
    }
}

impl Or for UpwardsClosedSet {
    fn or(mut self, other: Self) -> Self {
        if self.is_top() || other.is_top() {
            return Self::new_top();
        }

        if self.is_bot() {
            return other;
        }
        if other.is_bot() {
            return self;
        }

        self.clauses = self.clauses.or(other.clauses);
        self
    }
}
impl_bitor!(UpwardsClosedSet);

impl And for UpwardsClosedSet {
    fn and(self, other: Self) -> Self {
        if self.is_bot() || other.is_bot() {
            return UpwardsClosedSet::new_bot();
        }

        if self.is_top() {
            return other;
        }
        if other.is_top() {
            return self;
        }

        let aps = self
            .clauses
            .into_iter()
            .flat_map(|s_apc| {
                other
                    .clauses
                    .iter()
                    .map(move |o_apc| s_apc.clone() & o_apc.clone())
            })
            .collect();

        Self { clauses: aps }
    }
}
impl_bitand!(UpwardsClosedSet);

impl<C: SMTVariableContext<Location> + SMTVariableContext<Variable> + SMTVariableContext<Parameter>>
    EncodeToSMT<UpwardsClosedSet, C> for UpwardsClosedSet
{
    fn encode_to_smt_with_ctx(
        &self,
        solver: &taco_smt_encoder::SMTSolver,
        ctx: &C,
    ) -> Result<taco_smt_encoder::SMTExpr, SMTSolverError> {
        if self.clauses.is_empty() {
            return Ok(solver.false_());
        }

        let disjuncts = self
            .clauses
            .iter()
            .map(|c| c.encode_to_smt_with_ctx(solver, ctx))
            .collect::<Result<Vec<_>, SMTSolverError>>()?;

        Ok(solver.or_many(disjuncts))
    }
}

impl fmt::Display for UpwardsClosedSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", join_iterator(self.clauses.iter(), " || "))
    }
}

/// Errors that can occur when attempting to extract an upwards closed set of
/// configurations
#[derive(Debug, Clone, PartialEq)]
pub enum UpwardsClosedSetExtractionError {
    /// Found a constraint involving multiple locations, which is unsupported
    LocationConstraintMultiLocation(Box<(HashMap<Location, Fraction>, ThresholdConstraint)>),
    /// Specification uses non-linear expressions, therefore not upwards closed set can be extracted
    LIARewriteError(Box<ConstraintRewriteError>),
    /// Constraint on process in a specific location is not upwards closed
    /// (this can stem from constraints of the form `l < 42`)
    LocationConstraintNotUpwardsClosed(Box<(Location, ThresholdConstraint)>),
    /// Constraints on locations contain parameters
    LocationConstraintWithParameters(Box<(Location, ThresholdConstraint)>),
    /// Expression contains the temporal operator that is not being collapsed
    /// during extraction of the upwards closed set (e.g. a `<>` inside an
    /// `[]`-specification)
    NestedTemporalOperator,
}

impl From<ConstraintRewriteError> for UpwardsClosedSetExtractionError {
    fn from(err: ConstraintRewriteError) -> Self {
        Self::LIARewriteError(Box::new(err))
    }
}

impl fmt::Display for UpwardsClosedSetExtractionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UpwardsClosedSetExtractionError::LocationConstraintMultiLocation(cstr) => {
                write!(
                    f,
                    "Multiple locations referenced in constraint: {} {}",
                    join_iterator(cstr.0.iter().map(|(l, f)| format!("{f} * {l}")), "+ "),
                    cstr.1
                )
            }
            UpwardsClosedSetExtractionError::LIARewriteError(err) => {
                write!(f, "Failed to rewrite to linear arithmetic: {}", err)
            }
            UpwardsClosedSetExtractionError::LocationConstraintNotUpwardsClosed(x) => {
                write!(
                    f,
                    "Constraint on location '{}' not upwards closed. Constraint: {}{}",
                    x.0, x.0, x.1
                )
            }
            UpwardsClosedSetExtractionError::LocationConstraintWithParameters(x) => write!(
                f,
                "Constraint on location '{}' uses parameters. Constraint: {}{}",
                x.0, x.0, x.1
            ),
            UpwardsClosedSetExtractionError::NestedTemporalOperator => write!(
                f,
                "Expression contains the other temporal operator, which cannot be transformed into an upwards closed set"
            ),
        }
    }
}

impl std::error::Error for UpwardsClosedSetExtractionError {}

/// Description of an upwards closed set of configurations of a threshold
/// automaton
///
/// An upwards closed set of configurations can be seen as the conjunction of
/// three different types of constraints:
/// - a set of locations which are not allowed to contain any processes
/// - a map of locations to integer bounds, where the bounds represent minimal
///   the number of processes that need to be present in the respective location
/// - constraints on the shared variable evaluations
///
/// Any configuration of a threshold automaton that fulfills the constraints is
/// then said to be in the set.
///
/// This type should usually not be created directly. Instead, use the
/// [UpwardsClosedSet] type (with a single clause).
#[derive(Clone, Debug, PartialEq)]
pub struct UpwardsClosedClause {
    /// Location should not be covered by any processes
    locs_no_procs: HashSet<Location>,
    /// Map with location + number of processes at least in there
    locs_lower_bounds: HashMap<Location, u32>,
    /// conjunct of variable constraints
    variable_constr: LIAVariableConstraint,
}

impl UpwardsClosedClause {
    /// Get the constraint over the shared variable valuations
    pub fn variable_constr(&self) -> &LIAVariableConstraint {
        &self.variable_constr
    }

    /// Returns an iterator over locations and the respective lower bound on how
    /// many processes need to be in the location to be in the set
    pub fn locs_to_cover(&self) -> impl Iterator<Item = (&Location, &u32)> {
        self.locs_lower_bounds.iter()
    }

    /// Returns the locations where no process is allowed to be in
    pub fn locs_to_uncover(&self) -> impl Iterator<Item = &Location> {
        self.locs_no_procs.iter()
    }

    /// Create a new upwards closed set that contains all possible configurations
    pub fn new_top() -> Self {
        Self::new()
    }

    /// Check whether this clause is a tautology, i.e., contains all possible
    /// configurations
    pub fn is_top(&self) -> bool {
        self.locs_lower_bounds.is_empty()
            && self.locs_no_procs.is_empty()
            && self.variable_constr == LIAVariableConstraint::True
    }

    /// Creates a new empty set of atomic propositions
    ///
    /// Such an upwards closed set is equivalent to a constraint `true` or the
    /// set of all configurations
    fn new() -> Self {
        Self {
            locs_lower_bounds: HashMap::new(),
            locs_no_procs: HashSet::new(),
            variable_constr: LIAVariableConstraint::True,
        }
    }

    /// Add a locations where at least one process must be present
    ///
    /// If a lower bound constraint for a specific location has been previously
    /// added, this function will merge the constraints by taking the maximum of
    /// the lower bounds
    fn with_locs_to_cover<I: Borrow<Location>, L: IntoIterator<Item = I>>(
        mut self,
        cover: L,
    ) -> Self {
        cover.into_iter().for_each(|l| {
            if let Some(bound) = self.locs_lower_bounds.get_mut(l.borrow()) {
                *bound = max(*bound, 1);
                return;
            }

            self.locs_lower_bounds.insert(l.borrow().clone(), 1);
        });

        self
    }

    /// Add lower bounds for a set of locations
    ///
    /// If a lower bound constraint for a specific location has been previously
    /// added, this function will merge the constraints by taking the maximum of
    /// the lower bounds
    fn with_lower_bounds<I: Borrow<Location>, N: Into<u32>, L: IntoIterator<Item = (I, N)>>(
        mut self,
        cover: L,
    ) -> Self {
        cover.into_iter().for_each(|(l, n)| {
            if let Some(bound) = self.locs_lower_bounds.get_mut(l.borrow()) {
                *bound = max(*bound, n.into());
                return;
            }

            self.locs_lower_bounds.insert(l.borrow().clone(), n.into());
        });

        self
    }

    /// Add locations which are not allowed to be covered
    fn with_locs_to_empty<I: Borrow<Location>, L: IntoIterator<Item = I>>(
        mut self,
        locs: L,
    ) -> Self {
        locs.into_iter().for_each(|l| {
            self.locs_no_procs.insert(l.borrow().clone());
        });
        self
    }

    /// Add a constraint on the shared variable valuation
    ///
    /// If a constraint has been previously added, the resulting variable
    /// constraint will be the conjunction of the previous and the new one
    fn with_variable_constraint(mut self, constr: LIAVariableConstraint) -> Self {
        if constr == LIAVariableConstraint::True {
            return self;
        }

        if self.variable_constr == LIAVariableConstraint::True {
            self.variable_constr = constr;
            return self;
        }

        self.variable_constr = LIAVariableConstraint::BinaryGuard(
            Box::new(self.variable_constr),
            BooleanConnective::And,
            Box::new(constr),
        );

        self
    }

    /// Check whether the upwards closed set contains a reachability constraint,
    /// i.e., a constraint where at least one location is not allowed to be
    /// covered
    fn contains_reachability_constraint(&self) -> bool {
        !self.locs_no_procs.is_empty()
    }
}

impl TASpecification for UpwardsClosedClause {
    fn locs_appearing(&self) -> impl IntoIterator<Item = &Location> {
        self.locs_lower_bounds
            .keys()
            .chain(self.locs_no_procs.iter())
    }

    fn var_constraint(&self) -> impl IntoIterator<Item = &LIAVariableConstraint> {
        [&self.variable_constr]
    }
}

impl_bitand!(UpwardsClosedClause);

impl And for UpwardsClosedClause {
    fn and(self, other: Self) -> Self {
        self.with_lower_bounds(other.locs_lower_bounds.iter().map(|(l, n)| (l, *n)))
            .with_locs_to_empty(other.locs_no_procs)
            .with_variable_constraint(other.variable_constr)
    }
}

impl fmt::Display for UpwardsClosedClause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lower_bounds = join_iterator(
            self.locs_lower_bounds
                .iter()
                .map(|(loc, n)| format!("({loc} >= {n})"))
                .chain(self.locs_no_procs.iter().map(|loc| format!("({loc} == 0)"))),
            " && ",
        );

        write!(f, "{lower_bounds}")?;

        if self.variable_constr != LIAVariableConstraint::True {
            if !lower_bounds.is_empty() {
                write!(f, " && ")?;
            }
            write!(f, "{}", self.variable_constr)?;
        }

        Ok(())
    }
}

impl<C: SMTVariableContext<Location> + SMTVariableContext<Variable> + SMTVariableContext<Parameter>>
    EncodeToSMT<UpwardsClosedClause, C> for UpwardsClosedClause
{
    fn encode_to_smt_with_ctx(
        &self,
        solver: &taco_smt_encoder::SMTSolver,
        ctx: &C,
    ) -> Result<taco_smt_encoder::SMTExpr, SMTSolverError> {
        // lower bounds
        let lower_bounds = self
            .locs_lower_bounds
            .iter()
            .map(|(loc, n)| {
                let loc = ctx.get_expr_for(loc)?;
                let n = solver.numeral(*n);

                Ok(solver.gte(loc, n))
            })
            .collect::<Result<Vec<_>, SMTSolverError>>()?;

        // locations that should not be covered
        let loc_uncover = self
            .locs_no_procs
            .iter()
            .map(|loc| {
                let loc = ctx.get_expr_for(loc)?;
                let zero = solver.numeral(0);

                Ok(solver.eq(loc, zero))
            })
            .collect::<Result<Vec<_>, SMTSolverError>>()?;

        // constraint on variable evaluation
        let var_constr = self
            .variable_constr
            .as_boolean_expr()
            .encode_to_smt_with_ctx(solver, ctx)?;

        let res = solver.and_many(
            lower_bounds
                .into_iter()
                .chain(loc_uncover)
                .chain([var_constr]),
        );

        Ok(res)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{HashMap, HashSet};

    use taco_smt_encoder::{
        SMTSolverBuilder, SMTSolverContext,
        expression_encoding::{EncodeToSMT, SMTVariableContext, StaticSMTContext},
    };
    use taco_threshold_automaton::{
        BooleanVarConstraint,
        expressions::{ComparisonOp, IntegerExpression, IntegerOp, Location, Parameter, Variable},
        lia_threshold_automaton::{
            LIAVariableConstraint, integer_thresholds::DeriveFromIntegerComp,
        },
    };

    use crate::{
        TASpecification,
        internal_spec::upwards_closed_set::{
            UpwardsClosedClause, UpwardsClosedSet, UpwardsClosedSetExtractionError,
        },
    };

    #[test]
    fn test_target_config_new_cover() {
        let cover = UpwardsClosedSet::new_cover([
            Location::new("l1"),
            Location::new("l2"),
            Location::new("l3"),
        ]);

        let expected = UpwardsClosedSet {
            clauses: [UpwardsClosedClause {
                locs_lower_bounds: HashMap::from([
                    (Location::new("l1"), 1),
                    (Location::new("l2"), 1),
                    (Location::new("l3"), 1),
                ]),
                locs_no_procs: HashSet::new(),
                variable_constr: LIAVariableConstraint::True,
            }]
            .into(),
        };

        assert_eq!(cover, expected);
    }

    #[test]
    fn test_target_config_new_reach() {
        let reach = UpwardsClosedSet::new_reach(
            [
                (Location::new("l1"), 1),
                (Location::new("l2"), 1),
                (Location::new("l3"), 1),
            ],
            [
                Location::new("l4"),
                Location::new("l5"),
                Location::new("l6"),
            ],
        );

        let expected = UpwardsClosedSet {
            clauses: [UpwardsClosedClause {
                locs_lower_bounds: HashMap::from([
                    (Location::new("l1"), 1),
                    (Location::new("l2"), 1),
                    (Location::new("l3"), 1),
                ]),
                locs_no_procs: HashSet::from([
                    Location::new("l4"),
                    Location::new("l5"),
                    Location::new("l6"),
                ]),
                variable_constr: LIAVariableConstraint::True,
            }]
            .into(),
        };

        assert_eq!(reach, expected);
    }

    // This test tests a private method but this method is crucial for correctness
    #[test]
    fn test_disjunct_from_integer() {
        // l == 0
        let got = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        );
        assert!(got.is_ok());

        let expected = UpwardsClosedSet {
            clauses: [UpwardsClosedClause {
                locs_lower_bounds: HashMap::new(),
                locs_no_procs: HashSet::from([Location::new("l")]),
                variable_constr: LIAVariableConstraint::True,
            }]
            .into(),
        };

        assert_eq!(got.unwrap(), expected);

        // l != 0
        let got = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Neq,
            IntegerExpression::Const(0),
        );
        assert!(got.is_ok());

        let expected = UpwardsClosedSet {
            clauses: [UpwardsClosedClause {
                locs_lower_bounds: HashMap::from([(Location::new("l"), 1)]),
                locs_no_procs: HashSet::new(),
                variable_constr: LIAVariableConstraint::True,
            }]
            .into(),
        };

        assert_eq!(got.unwrap(), expected);

        // l > 0
        let got = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Gt,
            IntegerExpression::Const(0),
        );
        assert!(got.is_ok());

        let expected = UpwardsClosedSet {
            clauses: [UpwardsClosedClause {
                locs_lower_bounds: HashMap::from([(Location::new("l"), 1)]),
                locs_no_procs: HashSet::new(),
                variable_constr: LIAVariableConstraint::True,
            }]
            .into(),
        };

        assert_eq!(got.unwrap(), expected);

        // l > 42
        let got = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Gt,
            IntegerExpression::Const(42),
        );
        assert!(got.is_ok());

        let expected = UpwardsClosedSet {
            clauses: [UpwardsClosedClause {
                locs_lower_bounds: HashMap::from([(Location::new("l"), 43)]),
                locs_no_procs: HashSet::new(),
                variable_constr: LIAVariableConstraint::True,
            }]
            .into(),
        };

        assert_eq!(got.unwrap(), expected);

        // l >= 42
        let got = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Geq,
            IntegerExpression::Const(42),
        );
        assert!(got.is_ok());

        let expected = UpwardsClosedSet {
            clauses: [UpwardsClosedClause {
                locs_lower_bounds: HashMap::from([(Location::new("l"), 42)]),
                locs_no_procs: HashSet::new(),
                variable_constr: LIAVariableConstraint::True,
            }]
            .into(),
        };

        assert_eq!(got.unwrap(), expected);

        // l > 2/3
        let got = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Gt,
            IntegerExpression::BinaryExpr(
                Box::new(IntegerExpression::Const(2)),
                IntegerOp::Div,
                Box::new(IntegerExpression::Const(3)),
            ),
        );
        assert!(got.is_ok());

        let expected = UpwardsClosedSet {
            clauses: [UpwardsClosedClause {
                locs_lower_bounds: HashMap::from([(Location::new("l"), 1)]),
                locs_no_procs: HashSet::new(),
                variable_constr: LIAVariableConstraint::True,
            }]
            .into(),
        };

        assert_eq!(got.unwrap(), expected);

        // l >= 2/3
        let got = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Geq,
            IntegerExpression::BinaryExpr(
                Box::new(IntegerExpression::Const(2)),
                IntegerOp::Div,
                Box::new(IntegerExpression::Const(3)),
            ),
        );
        assert!(got.is_ok());

        let expected = UpwardsClosedSet {
            clauses: [UpwardsClosedClause {
                locs_lower_bounds: HashMap::from([(Location::new("l"), 1)]),
                locs_no_procs: HashSet::new(),
                variable_constr: LIAVariableConstraint::True,
            }]
            .into(),
        };

        assert_eq!(got.unwrap(), expected);

        //  42 < l --> l > 42
        let got = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Const(42),
            ComparisonOp::Lt,
            IntegerExpression::Atom(Location::new("l")),
        );
        assert!(got.is_ok(), "{:#?}", got);

        let expected = UpwardsClosedSet {
            clauses: [UpwardsClosedClause {
                locs_lower_bounds: HashMap::from([(Location::new("l"), 43)]),
                locs_no_procs: HashSet::new(),
                variable_constr: LIAVariableConstraint::True,
            }]
            .into(),
        };

        assert_eq!(got.unwrap(), expected);

        // l > 0 + 1 + 2
        let got = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Gt,
            IntegerExpression::BinaryExpr(
                Box::new(IntegerExpression::Const(0)),
                IntegerOp::Add,
                Box::new(IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::Const(1)),
                    IntegerOp::Add,
                    Box::new(IntegerExpression::Const(2)),
                )),
            ),
        );
        assert!(got.is_ok());

        let expected = UpwardsClosedSet {
            clauses: [UpwardsClosedClause {
                locs_lower_bounds: HashMap::from([(Location::new("l"), 4)]),
                locs_no_procs: HashSet::new(),
                variable_constr: LIAVariableConstraint::True,
            }]
            .into(),
        };

        assert_eq!(got.unwrap(), expected);

        // l < 1
        let got = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Lt,
            IntegerExpression::Const(1),
        );
        assert!(got.is_ok());

        let expected = UpwardsClosedSet {
            clauses: [UpwardsClosedClause {
                locs_lower_bounds: HashMap::new(),
                locs_no_procs: HashSet::from([Location::new("l")]),
                variable_constr: LIAVariableConstraint::True,
            }]
            .into(),
        };

        assert_eq!(got.unwrap(), expected);

        // l <= 0
        let got = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Leq,
            IntegerExpression::Const(0),
        );
        assert!(got.is_ok());

        let expected = UpwardsClosedSet {
            clauses: [UpwardsClosedClause {
                locs_lower_bounds: HashMap::new(),
                locs_no_procs: HashSet::from([Location::new("l")]),
                variable_constr: LIAVariableConstraint::True,
            }]
            .into(),
        };

        assert_eq!(got.unwrap(), expected);
    }

    // This test tests a private method but this method is crucial for correctness
    #[test]
    fn test_target_config_try_loc_constr_error_cases() {
        // l1 + l2 == 0
        let got = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::BinaryExpr(
                Box::new(IntegerExpression::Atom(Location::new("l1"))),
                IntegerOp::Add,
                Box::new(IntegerExpression::Atom(Location::new("l2"))),
            ),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        );
        assert!(got.is_err(), "{:#?}", got);

        assert!(matches!(
            got.unwrap_err(),
            UpwardsClosedSetExtractionError::LocationConstraintMultiLocation(_)
        ));

        // l * l == 0
        let got = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::BinaryExpr(
                Box::new(IntegerExpression::Atom(Location::new("l"))),
                IntegerOp::Mul,
                Box::new(IntegerExpression::Atom(Location::new("l"))),
            ),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        );
        assert!(got.is_err(), "{:#?}", got);

        assert!(matches!(
            got.unwrap_err(),
            UpwardsClosedSetExtractionError::LIARewriteError(_)
        ));

        // l + n == 0
        let got = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::BinaryExpr(
                Box::new(IntegerExpression::Atom(Location::new("l"))),
                IntegerOp::Add,
                Box::new(IntegerExpression::Param(Parameter::new("n"))),
            ),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        );
        assert!(got.is_err(), "{:#?}", got);

        assert!(matches!(
            got.unwrap_err(),
            UpwardsClosedSetExtractionError::LocationConstraintWithParameters(_)
        ));

        // l < 3
        let got = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Lt,
            IntegerExpression::Const(3),
        );
        assert!(got.is_err(), "{:#?}", got);

        assert!(matches!(
            got.unwrap_err(),
            UpwardsClosedSetExtractionError::LocationConstraintNotUpwardsClosed(_)
        ));

        // l <= 3
        let got = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Leq,
            IntegerExpression::Const(3),
        );
        assert!(got.is_err(), "{:#?}", got);

        assert!(matches!(
            got.unwrap_err(),
            UpwardsClosedSetExtractionError::LocationConstraintNotUpwardsClosed(_)
        ));

        // l == 3
        let got = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Eq,
            IntegerExpression::Const(3),
        );
        assert!(got.is_err(), "{:#?}", got);

        assert!(matches!(
            got.unwrap_err(),
            UpwardsClosedSetExtractionError::LocationConstraintNotUpwardsClosed(_)
        ));

        // l != 3
        let got = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Neq,
            IntegerExpression::Const(3),
        );
        assert!(got.is_err(), "{:#?}", got);

        assert!(matches!(
            got.unwrap_err(),
            UpwardsClosedSetExtractionError::LocationConstraintNotUpwardsClosed(_)
        ));
    }

    #[test]
    fn test_target_config_encode_target_config_unconstrained() {
        let solver_builder = SMTSolverBuilder::default();

        let ctx = StaticSMTContext::new(solver_builder, [], [], []).unwrap();

        let config = UpwardsClosedSet::new_top();

        let got_expr = config
            .encode_to_smt_with_ctx(ctx.get_smt_solver(), &ctx)
            .unwrap();

        let expected_expr = ctx.get_true();
        assert_eq!(got_expr, expected_expr)
    }

    #[test]
    fn test_target_config_encode_target_config_single_loc_cov() {
        let solver_builder = SMTSolverBuilder::default();

        let ctx = StaticSMTContext::new(solver_builder, [], [Location::new("l")], []).unwrap();

        let config = UpwardsClosedSet::new_cover([Location::new("l")]);

        let got_expr = config
            .encode_to_smt_with_ctx(ctx.get_smt_solver(), &ctx)
            .unwrap();

        let solver = ctx.get_smt_solver();

        let expected_expr = solver.and(
            solver.gte(
                ctx.get_expr_for(&Location::new("l")).unwrap(),
                solver.numeral(1),
            ),
            solver.true_(),
        );

        assert_eq!(
            got_expr,
            expected_expr,
            "got: {}, expected: {}",
            solver.display(got_expr),
            solver.display(expected_expr)
        )
    }

    #[test]
    fn test_target_config_encode_target_config_single_loc_uncover() {
        let solver_builder = SMTSolverBuilder::default();

        let ctx = StaticSMTContext::new(solver_builder, [], [Location::new("l")], []).unwrap();

        let config = UpwardsClosedSet::new_reach([], [Location::new("l")]);

        let got_expr = config
            .encode_to_smt_with_ctx(ctx.get_smt_solver(), &ctx)
            .unwrap();

        let solver = ctx.get_smt_solver();

        let expected_expr = solver.and(
            solver.eq(
                ctx.get_expr_for(&Location::new("l")).unwrap(),
                solver.numeral(0),
            ),
            solver.true_(),
        );

        assert_eq!(
            got_expr,
            expected_expr,
            "got: {}, expected: {}",
            solver.display(got_expr),
            solver.display(expected_expr)
        )
    }

    #[test]
    fn test_target_config_encode_target_config_var_constr() {
        let solver_builder = SMTSolverBuilder::default();

        let ctx = StaticSMTContext::new(
            solver_builder,
            [],
            [Location::new("l")],
            [Variable::new("v")],
        )
        .unwrap();

        let config = UpwardsClosedSet::new_var_constraint(
            BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            )
            .try_into()
            .unwrap(),
        );

        let got_expr = config
            .encode_to_smt_with_ctx(ctx.get_smt_solver(), &ctx)
            .unwrap();

        let solver = ctx.get_smt_solver();

        let expected_expr = solver.and(
            solver.lte(
                ctx.get_expr_for(&Variable::new("v")).unwrap(),
                solver.numeral(1),
            ),
            solver.gte(
                ctx.get_expr_for(&Variable::new("v")).unwrap(),
                solver.numeral(1),
            ),
        );

        assert_eq!(
            got_expr,
            expected_expr,
            "got: {}, expected: {}",
            solver.display(got_expr),
            solver.display(expected_expr)
        )
    }

    #[test]
    fn test_target_config_encode_target_config_all_constr() {
        let solver_builder = SMTSolverBuilder::default();

        let ctx = StaticSMTContext::new(
            solver_builder,
            [],
            [Location::new("l1"), Location::new("l2")],
            [Variable::new("v")],
        )
        .unwrap();

        let config =
            UpwardsClosedSet::new_reach([(Location::new("l1"), 42)], [Location::new("l2")])
                & UpwardsClosedSet::new_var_constraint(
                    BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("v"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(1)),
                    )
                    .try_into()
                    .unwrap(),
                );
        let got_expr = config
            .encode_to_smt_with_ctx(ctx.get_smt_solver(), &ctx)
            .unwrap();

        let solver = ctx.get_smt_solver();

        let expected_expr = solver.and_many([
            solver.gte(
                ctx.get_expr_for(&Location::new("l1")).unwrap(),
                solver.numeral(42),
            ),
            solver.eq(
                ctx.get_expr_for(&Location::new("l2")).unwrap(),
                solver.numeral(0),
            ),
            solver.and(
                solver.lte(
                    ctx.get_expr_for(&Variable::new("v")).unwrap(),
                    solver.numeral(1),
                ),
                solver.gte(
                    ctx.get_expr_for(&Variable::new("v")).unwrap(),
                    solver.numeral(1),
                ),
            ),
        ]);

        assert_eq!(
            got_expr,
            expected_expr,
            "got: {}, expected: {}",
            solver.display(got_expr),
            solver.display(expected_expr)
        )
    }

    #[test]
    fn test_target_config_locations_appearing() {
        let config =
            UpwardsClosedSet::new_reach([(Location::new("l1"), 42)], [Location::new("l2")])
                & UpwardsClosedSet::new_var_constraint(
                    BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("v"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(1)),
                    )
                    .try_into()
                    .unwrap(),
                );

        let got_expr: HashSet<Location> = config.locs_appearing().into_iter().cloned().collect();

        let expected_locs = HashSet::from([Location::new("l1"), Location::new("l2")]);

        assert_eq!(got_expr, expected_locs)
    }

    #[test]
    fn test_target_config_is_reachability_constr() {
        let config =
            UpwardsClosedSet::new_reach([(Location::new("l1"), 42)], [Location::new("l2")])
                & UpwardsClosedSet::new_var_constraint(
                    BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("v"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(1)),
                    )
                    .try_into()
                    .unwrap(),
                );

        assert!(config.contains_reachability_constraint());

        let config = UpwardsClosedSet::new_reach([(Location::new("l1"), 42)], [])
            & UpwardsClosedSet::new_var_constraint(
                BooleanVarConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("v"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(1)),
                )
                .try_into()
                .unwrap(),
            );

        assert!(!config.contains_reachability_constraint());
    }

    #[test]
    fn test_disjunction_target_config_get_locations_in_target() {
        let config1 =
            UpwardsClosedSet::new_reach([(Location::new("l1"), 42)], [Location::new("l2")])
                & UpwardsClosedSet::new_var_constraint(
                    BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("v"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(1)),
                    )
                    .try_into()
                    .unwrap(),
                );

        let config2 =
            UpwardsClosedSet::new_reach([(Location::new("l3"), 42)], [Location::new("l4")])
                & UpwardsClosedSet::new_var_constraint(
                    BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("v"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(1)),
                    )
                    .try_into()
                    .unwrap(),
                );

        let dis = config1 | config2;

        let got_set_locations: HashSet<Location> =
            dis.locs_appearing().into_iter().cloned().collect();

        let expected_set_locations = HashSet::from([
            Location::new("l1"),
            Location::new("l2"),
            Location::new("l3"),
            Location::new("l4"),
        ]);

        assert_eq!(got_set_locations, expected_set_locations);

        let dis = UpwardsClosedSet::new_bot();

        let got_set_locations: HashSet<_> = dis.locs_appearing().into_iter().collect();

        let expected_set_locations = HashSet::from([]);

        assert_eq!(got_set_locations, expected_set_locations);
    }

    #[test]
    fn test_disj_target_config_contains_reachability_constraint() {
        let config1 = UpwardsClosedSet::new_reach([(Location::new("l1"), 42)], [])
            & UpwardsClosedSet::new_var_constraint(
                BooleanVarConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("v"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(1)),
                )
                .try_into()
                .unwrap(),
            );

        let config2 =
            UpwardsClosedSet::new_reach([(Location::new("l3"), 42)], [Location::new("l4")])
                & UpwardsClosedSet::new_var_constraint(
                    BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("v"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(1)),
                    )
                    .try_into()
                    .unwrap(),
                );

        let dis = config1 | config2;

        assert!(dis.contains_reachability_constraint());

        let disj = UpwardsClosedSet::new_bot();

        assert!(!disj.contains_reachability_constraint())
    }

    #[test]
    fn test_disj_target_config_encode_to_smt_empty() {
        let solver_builder = SMTSolverBuilder::default();

        let ctx = StaticSMTContext::new(solver_builder, [], [], []).unwrap();

        let solver = ctx.get_smt_solver();

        let disj = UpwardsClosedSet::new_bot();

        let got_expr = disj.encode_to_smt_with_ctx(solver, &ctx).unwrap();

        let expected_expr = solver.false_();

        assert_eq!(
            got_expr,
            expected_expr,
            "got: {}, expected: {}",
            solver.display(got_expr),
            solver.display(expected_expr)
        )
    }

    #[test]
    fn test_disj_target_config_encode_smt() {
        let solver_builder = SMTSolverBuilder::default();

        let ctx = StaticSMTContext::new(
            solver_builder,
            [],
            [
                Location::new("l1"),
                Location::new("l2"),
                Location::new("l3"),
                Location::new("l4"),
            ],
            [Variable::new("v")],
        )
        .unwrap();

        let solver = ctx.get_smt_solver();

        let config1 =
            UpwardsClosedSet::new_reach([(Location::new("l1"), 42)], [Location::new("l2")])
                & UpwardsClosedSet::new_var_constraint(
                    BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("v"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(1)),
                    )
                    .try_into()
                    .unwrap(),
                );

        let config2 =
            UpwardsClosedSet::new_reach([(Location::new("l3"), 42)], [Location::new("l4")])
                & UpwardsClosedSet::new_var_constraint(
                    BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("v"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(1)),
                    )
                    .try_into()
                    .unwrap(),
                );

        let disj = config1 | config2;

        let got_expr = disj.encode_to_smt_with_ctx(solver, &ctx).unwrap();

        let expected_expr = solver.or_many([
            solver.and_many([
                solver.gte(
                    ctx.get_expr_for(&Location::new("l1")).unwrap(),
                    solver.numeral(42),
                ),
                solver.eq(
                    ctx.get_expr_for(&Location::new("l2")).unwrap(),
                    solver.numeral(0),
                ),
                solver.and(
                    solver.lte(
                        ctx.get_expr_for(&Variable::new("v")).unwrap(),
                        solver.numeral(1),
                    ),
                    solver.gte(
                        ctx.get_expr_for(&Variable::new("v")).unwrap(),
                        solver.numeral(1),
                    ),
                ),
            ]),
            solver.and_many([
                solver.gte(
                    ctx.get_expr_for(&Location::new("l3")).unwrap(),
                    solver.numeral(42),
                ),
                solver.eq(
                    ctx.get_expr_for(&Location::new("l4")).unwrap(),
                    solver.numeral(0),
                ),
                solver.and(
                    solver.lte(
                        ctx.get_expr_for(&Variable::new("v")).unwrap(),
                        solver.numeral(1),
                    ),
                    solver.gte(
                        ctx.get_expr_for(&Variable::new("v")).unwrap(),
                        solver.numeral(1),
                    ),
                ),
            ]),
        ]);

        assert_eq!(
            got_expr,
            expected_expr,
            "got: {}, expected: {}",
            solver.display(got_expr),
            solver.display(expected_expr)
        )
    }

    #[test]
    fn test_or_with_top_and_bot() {
        let cover = UpwardsClosedSet::new_cover([Location::new("l1")]);

        // `top || x` is `top`
        assert_eq!(
            UpwardsClosedSet::new_top() | cover.clone(),
            UpwardsClosedSet::new_top()
        );
        assert_eq!(
            cover.clone() | UpwardsClosedSet::new_top(),
            UpwardsClosedSet::new_top()
        );

        // `bot || x` is `x`
        assert_eq!(UpwardsClosedSet::new_bot() | cover.clone(), cover);
        assert_eq!(cover.clone() | UpwardsClosedSet::new_bot(), cover);
    }

    #[test]
    fn test_and_with_top_and_bot() {
        let cover = UpwardsClosedSet::new_cover([Location::new("l1")]);

        // `bot && x` is `bot`
        assert_eq!(
            UpwardsClosedSet::new_bot() & cover.clone(),
            UpwardsClosedSet::new_bot()
        );
        assert_eq!(
            cover.clone() & UpwardsClosedSet::new_bot(),
            UpwardsClosedSet::new_bot()
        );

        // `top && x` is `x`
        assert_eq!(UpwardsClosedSet::new_top() & cover.clone(), cover);
        assert_eq!(cover.clone() & UpwardsClosedSet::new_top(), cover);
    }

    #[test]
    fn test_from_integer_expr_rounding() {
        let l = Location::new("l");
        // `k * l <op> c`
        let mk = |k: u32, op: ComparisonOp, c: u32| {
            UpwardsClosedSet::from_integer_expr(
                IntegerExpression::Const(k) * IntegerExpression::Atom(l.clone()),
                op,
                IntegerExpression::Const(c),
            )
        };
        let empty = UpwardsClosedSet::new_from_clause(
            UpwardsClosedClause::new().with_locs_to_empty([l.clone()]),
        );

        // 2*l < 1, 2*l <= 1, 2*l < 2, l <= 0  ==>  l == 0
        assert_eq!(mk(2, ComparisonOp::Lt, 1), Ok(empty.clone()));
        assert_eq!(mk(2, ComparisonOp::Leq, 1), Ok(empty.clone()));
        assert_eq!(mk(2, ComparisonOp::Lt, 2), Ok(empty.clone()));
        assert_eq!(mk(1, ComparisonOp::Leq, 0), Ok(empty.clone()));

        // 2*l < 3 ==> l <= 1, which is not upwards closed
        assert!(matches!(
            mk(2, ComparisonOp::Lt, 3),
            Err(UpwardsClosedSetExtractionError::LocationConstraintNotUpwardsClosed(_))
        ));
        // 2*l <= 2 ==> l <= 1, which is not upwards closed
        assert!(matches!(
            mk(2, ComparisonOp::Leq, 2),
            Err(UpwardsClosedSetExtractionError::LocationConstraintNotUpwardsClosed(_))
        ));

        // l < 0 ==> bot
        assert_eq!(mk(1, ComparisonOp::Lt, 0), Ok(UpwardsClosedSet::new_bot()));

        // 2*l > 3, 2*l >= 3 ==> l >= 2
        let geq2 = UpwardsClosedSet::new_cover_int([(l.clone(), 2)]);
        assert_eq!(mk(2, ComparisonOp::Gt, 3), Ok(geq2.clone()));
        assert_eq!(mk(2, ComparisonOp::Geq, 3), Ok(geq2.clone()));
        // l > 1 ==> l >= 2
        assert_eq!(mk(1, ComparisonOp::Gt, 1), Ok(geq2));
        // l >= 0 ==> top
        assert_eq!(mk(1, ComparisonOp::Geq, 0), Ok(UpwardsClosedSet::new_top()));
    }
}
