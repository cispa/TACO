//! This module defines the `IndexCtx` type that serves as a mapping from
//! indices (`usize`) to elements in an [`IntervalThresholdAutomaton`].
//!
//! It enables to use vectors instead of maps in order to save on memory.

use std::collections::HashMap;

use taco_interval_ta::{IntervalThresholdAutomaton, interval::Interval};

use taco_threshold_automaton::{
    ThresholdAutomaton,
    expressions::{Location, Variable},
};

use crate::acs_threshold_automaton::{ACSInterval, ACSLocation, CSVariable};

/// Context providing a mapping from locations, variables and intervals to
/// indices or in this case types that can be used as indices
#[derive(Debug, Clone, PartialEq)]
pub struct IndexCtx {
    /// Map from [`Location`]s to [`ACSLocation`]s
    loc_to_index: HashMap<Location, ACSLocation>,
    /// Map from [`ACSLocation`]s to [`Location`]s
    index_to_loc: HashMap<ACSLocation, Location>,
    /// Map from [`Variable`]s to [`CSVariable`]s
    var_to_index: HashMap<Variable, CSVariable>,
    /// Map from [`CSVariable`]s to [`Variable`]s
    index_to_var: HashMap<CSVariable, Variable>,
    /// Map from a [`CSVariable`] and an [`Interval`] to [`ACSInterval`]
    interval_to_index: Vec<HashMap<Interval, ACSInterval>>,
    /// Map from a [`CSVariable`] and an [`ACSInterval`] to an [`Interval`]
    index_to_interval: Vec<HashMap<ACSInterval, Interval>>,
}

impl IndexCtx {
    /// Create a new [`IndexCtx`] for the given interval threshold automaton
    pub fn new(ta: &IntervalThresholdAutomaton) -> Self {
        // Initialize index mappings
        let loc_to_index: HashMap<_, _> = ta
            .locations()
            .enumerate()
            .map(|(i, l)| (l.clone(), ACSLocation(i)))
            .collect();
        let index_to_loc = loc_to_index
            .iter()
            .map(|(l, csl)| (*csl, l.clone()))
            .collect();

        let var_to_index: HashMap<_, _> = ta
            .variables()
            .enumerate()
            .map(|(i, v)| (v.clone(), CSVariable(i)))
            .collect();
        let index_to_var = var_to_index
            .iter()
            .map(|(v, csv)| (*csv, v.clone()))
            .collect();

        let mut interval_to_index = vec![HashMap::new(); var_to_index.len()];
        let mut index_to_interval = vec![HashMap::new(); var_to_index.len()];

        for (var, cs_var) in var_to_index.iter() {
            interval_to_index[cs_var.0] = ta
                .get_intervals(var)
                .iter()
                .enumerate()
                .map(|(i, interval)| (interval.clone(), ACSInterval(i)))
                .collect();

            index_to_interval[cs_var.0] = interval_to_index[cs_var.0]
                .iter()
                .map(|(int, csint)| (*csint, int.clone()))
                .collect();
        }

        Self {
            loc_to_index,
            index_to_loc,
            var_to_index,
            index_to_var,
            interval_to_index,
            index_to_interval,
        }
    }

    /// Translate from a [`Location`] to the corresponding [`ACSLocation`]
    pub fn to_cs_loc(&self, loc: &Location) -> ACSLocation {
        self.loc_to_index[loc]
    }

    /// Translate from a [`ACSLocation`] to the corresponding [`Location`]
    pub fn get_loc(&self, loc: &ACSLocation) -> &Location {
        &self.index_to_loc[loc]
    }

    /// Iterate over all locations in the index
    pub fn locations(&self) -> impl Iterator<Item = (&Location, &ACSLocation)> {
        self.loc_to_index.iter()
    }

    /// Translate from a [`Variable`] to the corresponding [`CSVariable`]
    pub fn to_cs_var(&self, var: &Variable) -> CSVariable {
        self.var_to_index[var]
    }

    /// Translate from a [`CSVariable`] to the corresponding [`Variable`]
    pub fn get_var(&self, var: &CSVariable) -> &Variable {
        &self.index_to_var[var]
    }

    /// Iterate over all variables in the context
    pub fn variables(&self) -> impl Iterator<Item = (&Variable, &CSVariable)> {
        self.var_to_index.iter()
    }

    /// Translate from an [`Interval`] of [`CSVariable`] to the corresponding
    /// [`ACSInterval`]
    pub fn to_cs_interval(&self, var: &CSVariable, i: &Interval) -> ACSInterval {
        self.interval_to_index[var.0][i]
    }

    /// Translate from an [`ACSInterval`] of [`CSVariable`] to the corresponding
    /// [`Interval`]
    pub fn get_interval(&self, var: &CSVariable, i: &ACSInterval) -> &Interval {
        &self.index_to_interval[var.0][i]
    }

    /// Check whether the interval [`ACSInterval`] for variable [`CSVariable`]
    /// exists
    pub fn interval_exists(&self, var: &CSVariable, interval: ACSInterval) -> bool {
        interval.0 < self.interval_to_index[var.0].len()
    }

    /// Iterate over all intervals of the given [`CSVariable`]
    pub fn intervals(&self, var: &CSVariable) -> impl Iterator<Item = (&Interval, &ACSInterval)> {
        self.interval_to_index[var.0].iter()
    }
}

#[cfg(test)]
mod mock_objects {
    use std::collections::HashMap;

    use taco_interval_ta::interval::Interval;
    use taco_threshold_automaton::expressions::{Location, Variable};

    use crate::acs_threshold_automaton::{
        ACSInterval, ACSLocation, CSVariable, index_ctx::IndexCtx,
    };

    impl IndexCtx {
        /// Directly create a new indexctx for testing purposes
        pub fn new_mock(
            loc_to_index: HashMap<Location, ACSLocation>,
            var_to_index: HashMap<Variable, CSVariable>,
            interval_to_index: Vec<HashMap<Interval, ACSInterval>>,
        ) -> Self {
            Self {
                loc_to_index: loc_to_index.clone(),
                index_to_loc: loc_to_index.into_iter().map(|(k, v)| (v, k)).collect(),
                var_to_index: var_to_index.clone(),
                index_to_var: var_to_index.into_iter().map(|(k, v)| (v, k)).collect(),
                interval_to_index: interval_to_index.clone(),
                index_to_interval: interval_to_index
                    .into_iter()
                    .map(|inner| inner.into_iter().map(|(k, v)| (v, k)).collect())
                    .collect(),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use taco_interval_ta::{
        builder::IntervalTABuilder,
        interval::{Interval, IntervalBoundary},
    };

    use taco_smt_encoder::SMTSolverBuilder;
    use taco_threshold_automaton::{
        expressions::{
            BooleanExpression, ComparisonOp, IntegerExpression, Location, Parameter, Variable,
        },
        general_threshold_automaton::{
            Action,
            builder::{GeneralThresholdAutomatonBuilder, RuleBuilder},
        },
        lia_threshold_automaton::LIAThresholdAutomaton,
    };

    use crate::acs_threshold_automaton::{
        ACSInterval, ACSLocation, CSVariable, index_ctx::IndexCtx,
    };

    #[test]
    fn test_new_index_ctx() {
        let var = Variable::new("x");

        let rc = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Param(Parameter::new("n"))),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Const(3)),
        );

        let ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_variables([var.clone()])
            .unwrap()
            .with_locations([Location::new("l1")])
            .unwrap()
            .with_parameter(Parameter::new("n"))
            .unwrap()
            .initialize()
            .with_resilience_condition(rc.clone())
            .unwrap()
            .with_initial_location_constraint(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Location::new("l1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            ))
            .unwrap()
            .with_rule(
                RuleBuilder::new(0, Location::new("l1"), Location::new("l1"))
                    .with_guard(BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(var.clone())),
                        ComparisonOp::Geq,
                        Box::new(IntegerExpression::Const(3)),
                    ))
                    .with_action(
                        Action::new(
                            var.clone(),
                            IntegerExpression::Const(1) + IntegerExpression::Atom(var.clone()),
                        )
                        .unwrap(),
                    )
                    .build(),
            )
            .unwrap()
            .build();

        let lia_ta = LIAThresholdAutomaton::try_from(ta).unwrap();

        let mut interval_tas = IntervalTABuilder::new(lia_ta, SMTSolverBuilder::default(), vec![])
            .build()
            .unwrap();
        let interval_threshold_automaton = interval_tas.next().unwrap();
        assert!(interval_tas.next().is_none());

        let got_idx_ctx = IndexCtx::new(&interval_threshold_automaton);

        let expected_idx_ctx = IndexCtx {
            loc_to_index: HashMap::from([(Location::new("l1"), ACSLocation(0))]),
            index_to_loc: HashMap::from([(ACSLocation(0), Location::new("l1"))]),
            var_to_index: HashMap::from([(Variable::new("x"), CSVariable(0))]),
            index_to_var: HashMap::from([(CSVariable(0), Variable::new("x"))]),
            interval_to_index: vec![HashMap::from([
                (Interval::new_constant(0, 1), ACSInterval(0)),
                (Interval::new_constant(1, 3), ACSInterval(1)),
                (
                    Interval::new(
                        IntervalBoundary::from_const(3),
                        false,
                        IntervalBoundary::new_infty(),
                        true,
                    ),
                    ACSInterval(2),
                ),
            ])],
            index_to_interval: vec![HashMap::from([
                (ACSInterval(0), Interval::new_constant(0, 1)),
                (ACSInterval(1), Interval::new_constant(1, 3)),
                (
                    ACSInterval(2),
                    Interval::new(
                        IntervalBoundary::from_const(3),
                        false,
                        IntervalBoundary::new_infty(),
                        true,
                    ),
                ),
            ])],
        };

        assert_eq!(got_idx_ctx, expected_idx_ctx);
    }

    #[test]
    fn test_to_cs_loc() {
        let ctx = IndexCtx {
            loc_to_index: HashMap::from([
                (Location::new("l1"), ACSLocation(0)),
                (Location::new("l2"), ACSLocation(1)),
            ]),
            index_to_loc: HashMap::from([
                (ACSLocation(0), Location::new("l1")),
                (ACSLocation(1), Location::new("l2")),
            ]),
            var_to_index: HashMap::from([]),
            index_to_var: HashMap::from([]),
            interval_to_index: vec![],
            index_to_interval: vec![],
        };

        assert_eq!(ctx.to_cs_loc(&Location::new("l1")), ACSLocation(0));
        assert_eq!(ctx.to_cs_loc(&Location::new("l2")), ACSLocation(1));
    }

    #[test]
    fn test_from_cs_loc() {
        let ctx = IndexCtx {
            loc_to_index: HashMap::from([
                (Location::new("l1"), ACSLocation(0)),
                (Location::new("l2"), ACSLocation(1)),
            ]),
            index_to_loc: HashMap::from([
                (ACSLocation(0), Location::new("l1")),
                (ACSLocation(1), Location::new("l2")),
            ]),
            var_to_index: HashMap::from([]),
            index_to_var: HashMap::from([]),
            interval_to_index: vec![],
            index_to_interval: vec![],
        };

        assert_eq!(ctx.get_loc(&ACSLocation(0)), &Location::new("l1"));
        assert_eq!(ctx.get_loc(&ACSLocation(1)), &Location::new("l2"));
    }

    #[test]
    fn test_locations() {
        let ctx = IndexCtx {
            loc_to_index: HashMap::from([
                (Location::new("l1"), ACSLocation(0)),
                (Location::new("l2"), ACSLocation(1)),
            ]),
            index_to_loc: HashMap::from([
                (ACSLocation(0), Location::new("l1")),
                (ACSLocation(1), Location::new("l2")),
            ]),
            var_to_index: HashMap::from([]),
            index_to_var: HashMap::from([]),
            interval_to_index: vec![],
            index_to_interval: vec![],
        };

        assert_eq!(
            ctx.locations().collect::<HashMap<_, _>>(),
            HashMap::from([
                (&Location::new("l1"), &ACSLocation(0)),
                (&Location::new("l2"), &ACSLocation(1)),
            ])
        );
    }

    #[test]
    fn test_to_cs_var() {
        let ctx = IndexCtx {
            loc_to_index: HashMap::from([]),
            index_to_loc: HashMap::from([]),
            var_to_index: HashMap::from([
                (Variable::new("x"), CSVariable(0)),
                (Variable::new("y"), CSVariable(1)),
            ]),
            index_to_var: HashMap::from([
                (CSVariable(0), Variable::new("x")),
                (CSVariable(1), Variable::new("y")),
            ]),
            interval_to_index: vec![],
            index_to_interval: vec![],
        };

        assert_eq!(ctx.to_cs_var(&Variable::new("x")), CSVariable(0));
        assert_eq!(ctx.to_cs_var(&Variable::new("y")), CSVariable(1));
    }

    #[test]
    fn test_from_cs_var() {
        let ctx = IndexCtx {
            loc_to_index: HashMap::from([]),
            index_to_loc: HashMap::from([]),
            var_to_index: HashMap::from([
                (Variable::new("x"), CSVariable(0)),
                (Variable::new("y"), CSVariable(1)),
            ]),
            index_to_var: HashMap::from([
                (CSVariable(0), Variable::new("x")),
                (CSVariable(1), Variable::new("y")),
            ]),
            interval_to_index: vec![],
            index_to_interval: vec![],
        };

        assert_eq!(ctx.get_var(&CSVariable(0)), &Variable::new("x"));
        assert_eq!(ctx.get_var(&CSVariable(1)), &Variable::new("y"));
    }

    #[test]
    fn test_variables() {
        let ctx = IndexCtx {
            loc_to_index: HashMap::from([]),
            index_to_loc: HashMap::from([]),
            var_to_index: HashMap::from([
                (Variable::new("x"), CSVariable(0)),
                (Variable::new("y"), CSVariable(1)),
            ]),
            index_to_var: HashMap::from([
                (CSVariable(0), Variable::new("x")),
                (CSVariable(1), Variable::new("y")),
            ]),
            interval_to_index: vec![],
            index_to_interval: vec![],
        };

        assert_eq!(
            ctx.variables().collect::<HashMap<_, _>>(),
            HashMap::from([
                (&Variable::new("x"), &CSVariable(0)),
                (&Variable::new("y"), &CSVariable(1)),
            ])
        );
    }

    #[test]
    fn test_to_cs_interval() {
        let ctx = IndexCtx {
            loc_to_index: HashMap::from([]),
            index_to_loc: HashMap::from([]),
            var_to_index: HashMap::from([]),
            index_to_var: HashMap::from([]),
            interval_to_index: vec![
                HashMap::from([
                    (Interval::new_constant(0, 1), ACSInterval(0)),
                    (Interval::new_constant(1, 2), ACSInterval(1)),
                    (
                        Interval::new(
                            IntervalBoundary::from_const(2),
                            false,
                            IntervalBoundary::new_infty(),
                            true,
                        ),
                        ACSInterval(2),
                    ),
                ]),
                HashMap::from([
                    (Interval::new_constant(0, 1), ACSInterval(0)),
                    (
                        Interval::new(
                            IntervalBoundary::from_const(1),
                            false,
                            IntervalBoundary::new_infty(),
                            true,
                        ),
                        ACSInterval(1),
                    ),
                ]),
            ],
            index_to_interval: vec![
                HashMap::from([
                    (ACSInterval(0), Interval::new_constant(0, 1)),
                    (ACSInterval(1), Interval::new_constant(1, 2)),
                    (
                        ACSInterval(2),
                        Interval::new(
                            IntervalBoundary::from_const(2),
                            false,
                            IntervalBoundary::new_infty(),
                            true,
                        ),
                    ),
                ]),
                HashMap::from([
                    (ACSInterval(0), Interval::new_constant(0, 1)),
                    (
                        ACSInterval(1),
                        Interval::new(
                            IntervalBoundary::from_const(1),
                            false,
                            IntervalBoundary::new_infty(),
                            true,
                        ),
                    ),
                ]),
            ],
        };

        assert_eq!(
            ctx.to_cs_interval(&CSVariable(0), &Interval::new_constant(0, 1)),
            ACSInterval(0)
        );
        assert_eq!(
            ctx.to_cs_interval(&CSVariable(0), &Interval::new_constant(1, 2)),
            ACSInterval(1)
        );
        assert_eq!(
            ctx.to_cs_interval(
                &CSVariable(0),
                &Interval::new(
                    IntervalBoundary::from_const(2),
                    false,
                    IntervalBoundary::new_infty(),
                    true,
                ),
            ),
            ACSInterval(2)
        );
        assert_eq!(
            ctx.to_cs_interval(&CSVariable(1), &Interval::new_constant(0, 1)),
            ACSInterval(0)
        );
        assert_eq!(
            ctx.to_cs_interval(
                &CSVariable(1),
                &Interval::new(
                    IntervalBoundary::from_const(1),
                    false,
                    IntervalBoundary::new_infty(),
                    true,
                ),
            ),
            ACSInterval(1)
        );
    }

    #[test]
    fn test_from_cs_interval() {
        let ctx = IndexCtx {
            loc_to_index: HashMap::from([]),
            index_to_loc: HashMap::from([]),
            var_to_index: HashMap::from([]),
            index_to_var: HashMap::from([]),
            interval_to_index: vec![
                HashMap::from([
                    (Interval::new_constant(0, 1), ACSInterval(0)),
                    (Interval::new_constant(1, 2), ACSInterval(1)),
                    (
                        Interval::new(
                            IntervalBoundary::from_const(2),
                            false,
                            IntervalBoundary::new_infty(),
                            true,
                        ),
                        ACSInterval(2),
                    ),
                ]),
                HashMap::from([
                    (Interval::new_constant(0, 1), ACSInterval(0)),
                    (
                        Interval::new(
                            IntervalBoundary::from_const(1),
                            false,
                            IntervalBoundary::new_infty(),
                            true,
                        ),
                        ACSInterval(1),
                    ),
                ]),
            ],
            index_to_interval: vec![
                HashMap::from([
                    (ACSInterval(0), Interval::new_constant(0, 1)),
                    (ACSInterval(1), Interval::new_constant(1, 2)),
                    (
                        ACSInterval(2),
                        Interval::new(
                            IntervalBoundary::from_const(2),
                            false,
                            IntervalBoundary::new_infty(),
                            true,
                        ),
                    ),
                ]),
                HashMap::from([
                    (ACSInterval(0), Interval::new_constant(0, 1)),
                    (
                        ACSInterval(1),
                        Interval::new(
                            IntervalBoundary::from_const(1),
                            false,
                            IntervalBoundary::new_infty(),
                            true,
                        ),
                    ),
                ]),
            ],
        };

        assert_eq!(
            ctx.get_interval(&CSVariable(0), &ACSInterval(0)),
            &Interval::new_constant(0, 1)
        );
        assert_eq!(
            ctx.get_interval(&CSVariable(0), &ACSInterval(1)),
            &Interval::new_constant(1, 2)
        );
        assert_eq!(
            ctx.get_interval(&CSVariable(0), &ACSInterval(2)),
            &Interval::new(
                IntervalBoundary::from_const(2),
                false,
                IntervalBoundary::new_infty(),
                true,
            ),
        );
        assert_eq!(
            ctx.get_interval(&CSVariable(1), &ACSInterval(0)),
            &Interval::new_constant(0, 1)
        );
        assert_eq!(
            ctx.get_interval(&CSVariable(1), &ACSInterval(1)),
            &Interval::new(
                IntervalBoundary::from_const(1),
                false,
                IntervalBoundary::new_infty(),
                true,
            ),
        );
    }

    #[test]
    fn test_exists_interval() {
        let ctx = IndexCtx {
            loc_to_index: HashMap::from([]),
            index_to_loc: HashMap::from([]),
            var_to_index: HashMap::from([]),
            index_to_var: HashMap::from([]),
            interval_to_index: vec![
                HashMap::from([
                    (Interval::new_constant(0, 1), ACSInterval(0)),
                    (Interval::new_constant(1, 2), ACSInterval(1)),
                    (
                        Interval::new(
                            IntervalBoundary::from_const(2),
                            false,
                            IntervalBoundary::new_infty(),
                            true,
                        ),
                        ACSInterval(2),
                    ),
                ]),
                HashMap::from([
                    (Interval::new_constant(0, 1), ACSInterval(0)),
                    (
                        Interval::new(
                            IntervalBoundary::from_const(1),
                            false,
                            IntervalBoundary::new_infty(),
                            true,
                        ),
                        ACSInterval(1),
                    ),
                ]),
            ],
            index_to_interval: vec![
                HashMap::from([
                    (ACSInterval(0), Interval::new_constant(0, 1)),
                    (ACSInterval(1), Interval::new_constant(1, 2)),
                    (
                        ACSInterval(2),
                        Interval::new(
                            IntervalBoundary::from_const(2),
                            false,
                            IntervalBoundary::new_infty(),
                            true,
                        ),
                    ),
                ]),
                HashMap::from([
                    (ACSInterval(0), Interval::new_constant(0, 1)),
                    (
                        ACSInterval(1),
                        Interval::new(
                            IntervalBoundary::from_const(1),
                            false,
                            IntervalBoundary::new_infty(),
                            true,
                        ),
                    ),
                ]),
            ],
        };

        assert!(ctx.interval_exists(&CSVariable(0), ACSInterval(0)));
        assert!(ctx.interval_exists(&CSVariable(1), ACSInterval(0)));

        assert!(!ctx.interval_exists(&CSVariable(0), ACSInterval(5)));
        assert!(!ctx.interval_exists(&CSVariable(0), ACSInterval(3)));
    }

    #[test]
    fn test_intervals() {
        let ctx = IndexCtx {
            loc_to_index: HashMap::from([]),
            index_to_loc: HashMap::from([]),
            var_to_index: HashMap::from([]),
            index_to_var: HashMap::from([]),
            interval_to_index: vec![
                HashMap::from([
                    (Interval::new_constant(0, 1), ACSInterval(0)),
                    (Interval::new_constant(1, 2), ACSInterval(1)),
                    (
                        Interval::new(
                            IntervalBoundary::from_const(2),
                            false,
                            IntervalBoundary::new_infty(),
                            true,
                        ),
                        ACSInterval(2),
                    ),
                ]),
                HashMap::from([
                    (Interval::new_constant(0, 1), ACSInterval(0)),
                    (
                        Interval::new(
                            IntervalBoundary::from_const(1),
                            false,
                            IntervalBoundary::new_infty(),
                            true,
                        ),
                        ACSInterval(1),
                    ),
                ]),
            ],
            index_to_interval: vec![
                HashMap::from([
                    (ACSInterval(0), Interval::new_constant(0, 1)),
                    (ACSInterval(1), Interval::new_constant(1, 2)),
                    (
                        ACSInterval(2),
                        Interval::new(
                            IntervalBoundary::from_const(2),
                            false,
                            IntervalBoundary::new_infty(),
                            true,
                        ),
                    ),
                ]),
                HashMap::from([
                    (ACSInterval(0), Interval::new_constant(0, 1)),
                    (
                        ACSInterval(1),
                        Interval::new(
                            IntervalBoundary::from_const(1),
                            false,
                            IntervalBoundary::new_infty(),
                            true,
                        ),
                    ),
                ]),
            ],
        };

        assert_eq!(
            ctx.intervals(&CSVariable(0))
                .map(|(a, b)| (a.clone(), *b))
                .collect::<HashMap<_, _>>(),
            HashMap::from([
                (Interval::new_constant(0, 1), ACSInterval(0)),
                (Interval::new_constant(1, 2), ACSInterval(1)),
                (
                    Interval::new(
                        IntervalBoundary::from_const(2),
                        false,
                        IntervalBoundary::new_infty(),
                        true,
                    ),
                    ACSInterval(2),
                ),
            ])
        );
        assert_eq!(
            ctx.intervals(&CSVariable(1))
                .map(|(a, b)| (a.clone(), *b))
                .collect::<HashMap<_, _>>(),
            HashMap::from([
                (Interval::new_constant(0, 1), ACSInterval(0)),
                (
                    Interval::new(
                        IntervalBoundary::from_const(1),
                        false,
                        IntervalBoundary::new_infty(),
                        true,
                    ),
                    ACSInterval(1),
                ),
            ])
        );
    }
}
