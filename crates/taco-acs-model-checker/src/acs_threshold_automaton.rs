//! A ThresholdAutomaton representation for efficient operations on counter
//! systems and counter configurations
//!
//! This module and its submodule define the [`ACSThresholdAutomaton`] type,
//! along with the [`ACSTAConfig`] type, which are compact representations of
//! counter states in a threshold automaton.
//! The main goal of these types is to have a representation of configurations
//! with a small memory footprint, which allow for efficient computations of
//! (certain) predecessor configurations.
//!
//! Therefore, internally a configuration is just implemented as a vector of
//! integers, to indicate the current interval and the number of processes per
//! variable.
//!
//! These types correspond to the `ACS` described in the paper
//! [Parameterized Verification of Round-based Distributed Algorithms via
//! Extended Threshold Automata](https://arxiv.org/pdf/2406.19880)

use std::{collections::HashSet, fmt};

use taco_display_utils::indent_all;
use taco_interval_ta::{
    IntervalActionEffect, IntervalConstraint, IntervalTAAction, IntervalTARule,
    IntervalThresholdAutomaton,
};

use taco_threshold_automaton::{
    ActionDefinition, RuleDefinition, ThresholdAutomaton,
    expressions::{IsDeclared, Location, Parameter, Variable},
    general_threshold_automaton::Rule,
};

use crate::acs_threshold_automaton::{
    configuration::{ACSIntervalState, ACSTAConfig},
    index_ctx::IndexCtx,
};

pub mod configuration;
mod index_ctx;

/// A location in a [`ACSThresholdAutomaton`]
///
/// Such a location is internally only represents an index in the representation
/// of location state, i.e., it describes which position of the vector holds the
/// number of processes in its concrete counter part (a
/// [`Location`]).
///
/// The mapping from [`Location`] to [`ACSLocation`] is
/// maintained by the[`ACSThresholdAutomaton`]. It is important to not
/// mix [`ACSLocation`] of different automata as it can result in panics and
/// wrong results, as validation has been omitted for better performance.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ACSLocation(usize);

impl ACSLocation {
    /// Get a string representation of the location, i.e. the name of the
    /// corresponding [`Location`]
    pub fn display(&self, ta: &ACSThresholdAutomaton) -> String {
        ta.idx_ctx.get_loc(self).to_string()
    }
}

/// A variable in a [`ACSThresholdAutomaton`]
///
/// Such a variable is internally only represents an index in the representation
/// of an interval state, i.e., it describes which position of the vector holds
/// the value of the interval in its concrete counter part (a
/// [`Variable`]).
///
/// The mapping from [`Variable`] to [`CSVariable`] is
/// maintained by the[`ACSThresholdAutomaton`]. It is important to not
/// mix [`CSVariable`] of different automata as it can result in panics and
/// wrong results, as validation has been omitted for better performance.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CSVariable(usize);

impl CSVariable {
    /// Get a string representation of the variable, i.e., the name of the
    /// [`Variable`] this variable corresponds to
    pub fn display(&self, ta: &ACSThresholdAutomaton) -> String {
        ta.idx_ctx.get_var(self).to_string()
    }
}

/// An interval in a [`ACSThresholdAutomaton`]
///
/// Such a interval is internally only represents an integer, which is the index
/// of the interval in the current interval order. That is it describes the
/// index of an [`taco_interval_ta::interval::Interval`] for a
/// specific variable, as defined by the
/// [`IntervalThresholdAutomaton`].
///
/// It is important to not mix [`ACSInterval`] of different automata as it
/// can result in panics and wrong results, as validation has been omitted for
/// better performance.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ACSInterval(usize);

impl ACSInterval {
    /// Get a string representation of the interval, i.e., get the string
    /// representation of the corresponding
    /// [`taco_interval_ta::interval::Interval`]
    pub fn display(&self, var: &CSVariable, ta: &ACSThresholdAutomaton) -> String {
        ta.idx_ctx.get_interval(var, self).to_string()
    }
}

/// A variant of an [`IntervalThresholdAutomaton`] allowing for low-memory
/// representations of configurations (by a [`ACSTAConfig`]) and efficient
/// predecessor computations
///
/// This type is a variant of an [`IntervalThresholdAutomaton`] that translates
/// variables (see [`CSVariable`]), locations (see [`ACSLocation`]) and intervals
/// (see [`ACSInterval`]) into indices, that can then be used to in
/// [`ACSTAConfig`] instead of the corresponding concrete types. The mapping is
/// then maintained in this type.
///
/// Additionally, initial location configurations and intervals, as well
/// as rules (see [`CSRule`]) are already translated into operations on the
/// abstracted states, such that they do not need to be translated on the fly.
#[derive(Debug, Clone)]
pub struct ACSThresholdAutomaton {
    /// Main index maintaining the mapping of locations, variables and intervals
    idx_ctx: IndexCtx,
    /// [`IntervalThresholdAutomaton`] that this threshold automaton is an
    /// abstraction of
    interval_ta: IntervalThresholdAutomaton,
    /// Initial locations (as [`ACSLocation`]s)
    initial_locs: Vec<ACSLocation>,
    /// Initial intervals (as [`ACSInterval`]s, indexed by [`CSVariable`])
    initial_intervals: Vec<HashSet<ACSInterval>>,
    /// Rules operation on cs types
    rules: Vec<CSRule>,
}

impl ACSThresholdAutomaton {
    /// Create the corresponding [`ACSThresholdAutomaton`] from the given
    /// [`IntervalThresholdAutomaton`]
    pub fn new(interval_ta: IntervalThresholdAutomaton) -> Self {
        let idx_ctx = IndexCtx::new(&interval_ta);

        let initial_locs = interval_ta
            .locations()
            .filter(|loc| interval_ta.can_be_initial_location(loc))
            .map(|loc| idx_ctx.to_cs_loc(loc))
            .collect();

        let mut initial_intervals = vec![HashSet::new(); idx_ctx.variables().count()];
        for (var, var_cs) in idx_ctx.variables() {
            for interval in interval_ta.get_initial_interval(var) {
                initial_intervals[var_cs.0].insert(idx_ctx.to_cs_interval(var_cs, interval));
            }
        }

        let rules: Vec<_> = interval_ta
            .rules()
            .map(|r| CSRule::from_interval_rule(&idx_ctx, r))
            .collect();

        debug_assert!(
            !rules
                .iter()
                .any(|r1| rules.iter().any(|r2| r1.id() == r2.id() && r1 != r2)),
            "Rule ids in the threshold automaton must be unique"
        );

        Self {
            idx_ctx,
            interval_ta,
            initial_locs,
            initial_intervals,
            rules,
        }
    }

    /// Check whether the location is an initial location, i.e. processes can
    /// start in this location
    pub fn is_initial_loc(&self, loc: &ACSLocation) -> bool {
        self.initial_locs.contains(loc)
    }

    /// Check whether the interval `i` is an initial interval for variable
    /// `var`
    pub fn is_initial_interval(&self, var: &CSVariable, i: &ACSInterval) -> bool {
        self.initial_intervals[var.0].contains(i)
    }

    /// Get the zero interval for variable `var`
    pub fn get_zero_interval(&self, var: &CSVariable) -> ACSInterval {
        let zero_interval = self
            .interval_ta
            .get_zero_interval(self.idx_ctx.get_var(var));

        self.idx_ctx.to_cs_interval(var, zero_interval)
    }

    /// Get all intervals for the variable
    pub fn get_all_intervals<'a>(
        &'a self,
        var: &'a CSVariable,
    ) -> impl Iterator<Item = &'a ACSInterval> {
        self.idx_ctx.intervals(var).map(|(_, i)| i)
    }

    /// Get the previous interval
    pub fn get_prev_interval(
        &self,
        _var: &CSVariable,
        interval: &ACSInterval,
    ) -> Option<ACSInterval> {
        if interval.0 == 0 {
            return None;
        }

        // We rely on the fact that the interval indices  in `IndexCtx`
        // are created with respect to the interval order and that there are no
        // jumps. Therefore we can simply compute the predecessor on the index.
        //
        // The next assertion checks this invariant at runtime
        debug_assert!(
            self.interval_ta.get_previous_interval(
                self.idx_ctx.get_var(_var),
                self.idx_ctx.get_interval(_var, interval)
            ) == Some(
                self.idx_ctx
                    .get_interval(_var, &ACSInterval(interval.0 - 1))
            ),
            "IndexCtx was not initialized respecting the variable ordering"
        );

        Some(ACSInterval(interval.0 - 1))
    }

    /// Get the next interval
    pub fn get_next_interval(
        &self,
        var: &CSVariable,
        interval: &ACSInterval,
    ) -> Option<ACSInterval> {
        let res = ACSInterval(interval.0 + 1);

        if !self.idx_ctx.interval_exists(var, res) {
            return None;
        }

        // We rely on the fact that the interval indices  in `IndexCtx`
        // are created with respect to the interval order and that there are no
        // jumps. Therefore we can simply compute the predecessor on the index.
        //
        // The next assertion checks this invariant at runtime
        debug_assert!(
            self.interval_ta.get_next_interval(
                self.idx_ctx.get_var(var),
                self.idx_ctx.get_interval(var, interval)
            ) == Some(self.idx_ctx.get_interval(var, &res)),
            "IndexCtx was not initialized respecting the variable ordering"
        );

        Some(res)
    }

    /// Get all variables appearing in the threshold automaton
    pub fn variables(&self) -> impl Iterator<Item = &CSVariable> {
        self.idx_ctx.variables().map(|(_, v)| v)
    }

    /// Get all [`ACSLocation`]s of the automaton
    pub fn locations(&self) -> impl Iterator<Item = &ACSLocation> {
        self.idx_ctx.locations().map(|(_, loc)| loc)
    }

    /// Get all rules of the automaton
    pub fn rules(&self) -> impl Iterator<Item = &CSRule> {
        self.rules.iter()
    }

    /// Get rule by id
    pub fn get_rule_by_id(&self, id: u32) -> Option<&Rule> {
        self.interval_ta.get_ta().rules().find(|r| r.id() == id)
    }

    /// Get a reference to the interval threshold automaton the automaton
    /// has been derived from
    pub fn get_interval_ta(&self) -> &IntervalThresholdAutomaton {
        &self.interval_ta
    }
}

impl From<IntervalThresholdAutomaton> for ACSThresholdAutomaton {
    fn from(value: IntervalThresholdAutomaton) -> Self {
        Self::new(value)
    }
}

impl IsDeclared<Parameter> for ACSThresholdAutomaton {
    fn is_declared(&self, obj: &Parameter) -> bool {
        self.interval_ta.is_declared(obj)
    }
}

impl IsDeclared<Variable> for ACSThresholdAutomaton {
    fn is_declared(&self, obj: &Variable) -> bool {
        self.interval_ta.is_declared(obj)
    }
}

impl IsDeclared<Location> for ACSThresholdAutomaton {
    fn is_declared(&self, obj: &Location) -> bool {
        self.interval_ta.is_declared(obj)
    }
}

impl fmt::Display for ACSThresholdAutomaton {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "CSThresholdAutomaton {{\n {}\n}}",
            indent_all(self.interval_ta.to_string())
        )
    }
}

impl ThresholdAutomaton for ACSThresholdAutomaton {
    type Rule = IntervalTARule;

    type InitialVariableConstraintType = IntervalConstraint;

    fn name(&self) -> &str {
        self.interval_ta.name()
    }

    fn parameters(
        &self,
    ) -> impl Iterator<Item = &taco_threshold_automaton::expressions::Parameter> {
        self.interval_ta.parameters()
    }

    fn initial_location_constraints(
        &self,
    ) -> impl Iterator<Item = &taco_threshold_automaton::LocationConstraint> {
        self.interval_ta.initial_location_constraints()
    }

    fn initial_variable_constraints(
        &self,
    ) -> impl Iterator<Item = &Self::InitialVariableConstraintType> {
        self.interval_ta.initial_variable_constraints()
    }

    fn resilience_conditions(
        &self,
    ) -> impl Iterator<
        Item = &taco_threshold_automaton::expressions::BooleanExpression<
            taco_threshold_automaton::expressions::Parameter,
        >,
    > {
        self.interval_ta.resilience_conditions()
    }

    fn variables(&self) -> impl Iterator<Item = &taco_threshold_automaton::expressions::Variable> {
        self.interval_ta.variables()
    }

    fn locations(&self) -> impl Iterator<Item = &taco_threshold_automaton::expressions::Location> {
        self.interval_ta.locations()
    }

    fn can_be_initial_location(
        &self,
        location: &taco_threshold_automaton::expressions::Location,
    ) -> bool {
        self.interval_ta.can_be_initial_location(location)
    }

    fn rules(&self) -> impl Iterator<Item = &Self::Rule> {
        self.interval_ta.rules()
    }

    fn incoming_rules(
        &self,
        location: &taco_threshold_automaton::expressions::Location,
    ) -> impl Iterator<Item = &Self::Rule> {
        self.interval_ta.incoming_rules(location)
    }

    fn outgoing_rules(
        &self,
        location: &taco_threshold_automaton::expressions::Location,
    ) -> impl Iterator<Item = &Self::Rule> {
        self.interval_ta.outgoing_rules(location)
    }
}

/// Constraints on interval states operating on [`ACSInterval`]s and
/// [`CSVariable`]s
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CSIntervalConstraint {
    /// Always enabled
    True,
    /// Always disabled
    False,
    /// A conjunction of two [`CSIntervalConstraint`]s
    Conj(Box<CSIntervalConstraint>, Box<CSIntervalConstraint>),
    /// A disjunction of two [`CSIntervalConstraint`]s
    Disj(Box<CSIntervalConstraint>, Box<CSIntervalConstraint>),
    /// Constraint on an interval the variable should be in
    VarGuard(CSVariable, Vec<ACSInterval>),
}

impl CSIntervalConstraint {
    /// Translate from a [`IntervalConstraint`] to a [`CSIntervalConstraint`]
    fn from_interval_constr(ta_cs: &IndexCtx, ics: &IntervalConstraint) -> Self {
        match ics {
            IntervalConstraint::True => Self::True,
            IntervalConstraint::False => Self::False,
            IntervalConstraint::Conj(lhs, rhs) => {
                let lhs = Self::from_interval_constr(ta_cs, lhs);
                let rhs = Self::from_interval_constr(ta_cs, rhs);

                CSIntervalConstraint::Conj(Box::new(lhs), Box::new(rhs))
            }
            IntervalConstraint::Disj(lhs, rhs) => {
                let lhs = Self::from_interval_constr(ta_cs, lhs);
                let rhs = Self::from_interval_constr(ta_cs, rhs);

                CSIntervalConstraint::Disj(Box::new(lhs), Box::new(rhs))
            }
            IntervalConstraint::SingleVarIntervalConstr(var, intervals) => {
                let var = ta_cs.to_cs_var(var);
                let intervals = intervals
                    .iter()
                    .map(|i| ta_cs.to_cs_interval(&var, i))
                    .collect();

                CSIntervalConstraint::VarGuard(var, intervals)
            }
            IntervalConstraint::MultiVarIntervalConstr(_weighted_sum, _intervals) => todo!(),
        }
    }

    /// Check whether the given interval state satisfies the constraint
    fn is_satisfied(&self, interval_state: &ACSIntervalState) -> bool {
        match self {
            CSIntervalConstraint::True => true,
            CSIntervalConstraint::False => false,
            CSIntervalConstraint::Conj(lhs, rhs) => {
                lhs.is_satisfied(interval_state) && rhs.is_satisfied(interval_state)
            }
            CSIntervalConstraint::Disj(lhs, rhs) => {
                lhs.is_satisfied(interval_state) || rhs.is_satisfied(interval_state)
            }
            CSIntervalConstraint::VarGuard(var, intervals) => {
                intervals.contains(&interval_state[*var])
            }
        }
    }
}

/// Effect of the application of a [`CSRule`] on [`CSVariable`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CSIntervalAction {
    /// Variable
    var: CSVariable,
    /// Effect
    effect: IntervalActionEffect,
}

impl CSIntervalAction {
    /// Translate from an [`IntervalTAAction`] to a [`CSIntervalAction`]
    fn from_interval_action(ctx: &IndexCtx, act: &IntervalTAAction) -> Self {
        let var = ctx.to_cs_var(act.variable());
        Self {
            var,
            effect: act.effect().clone(),
        }
    }

    /// Get the variable the action is applied to
    pub fn variable(&self) -> &CSVariable {
        &self.var
    }

    /// Get the effect of the action
    pub fn effect(&self) -> &IntervalActionEffect {
        &self.effect
    }
}

/// Rule of a [`ACSThresholdAutomaton`] that can be directly applied to a the
/// cs types
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CSRule {
    /// Unique ID
    id: u32,
    /// Source location of the rule
    source: ACSLocation,
    /// target location of the rule
    target: ACSLocation,
    /// Guard of the rule
    guard: CSIntervalConstraint,
    /// Actions of the rule
    actions: Vec<CSIntervalAction>,
}

impl CSRule {
    /// Translate from an [`IntervalTARule`] to a [`CSRule`]
    fn from_interval_rule(ctx: &IndexCtx, r: &IntervalTARule) -> Self {
        let source = ctx.to_cs_loc(r.source());
        let target = ctx.to_cs_loc(r.target());
        let guard = CSIntervalConstraint::from_interval_constr(ctx, r.guard());
        let actions = r
            .actions()
            .map(|act| CSIntervalAction::from_interval_action(ctx, act))
            .collect();

        Self {
            id: r.id(),
            source,
            target,
            guard,
            actions,
        }
    }

    /// Check whether the rule is enabled in the current configuration
    pub fn is_enabled(&self, cfg: &ACSTAConfig) -> bool {
        self.guard.is_satisfied(cfg.interval_state()) && cfg.location_state()[self.source()] > 0
    }

    pub fn is_guard_enabled(&self, is: &ACSIntervalState) -> bool {
        self.guard.is_satisfied(is)
    }

    /// Get the id of the rule
    pub fn id(&self) -> u32 {
        self.id
    }

    /// Get the target of the rule
    pub fn target(&self) -> &ACSLocation {
        &self.target
    }

    /// Get the source location of the rule
    pub fn source(&self) -> &ACSLocation {
        &self.source
    }

    /// Get the actions of the rule
    pub fn actions(&self) -> impl Iterator<Item = &CSIntervalAction> {
        self.actions.iter()
    }

    /// Get the guard of the rule
    pub fn guard(&self) -> &CSIntervalConstraint {
        &self.guard
    }
}

#[cfg(test)]
mod mock_objects {

    use taco_threshold_automaton::expressions::{Location, Variable};

    use crate::acs_threshold_automaton::{
        ACSInterval, ACSLocation, ACSThresholdAutomaton, CSIntervalAction, CSIntervalConstraint,
        CSRule, CSVariable,
    };

    impl ACSLocation {
        pub fn new_mock(l: usize) -> Self {
            ACSLocation(l)
        }
    }

    impl CSVariable {
        pub fn new_mock(l: usize) -> Self {
            CSVariable(l)
        }
    }

    impl ACSInterval {
        pub fn new_mock(l: usize) -> Self {
            ACSInterval(l)
        }
    }

    impl CSRule {
        pub fn new_mock(
            id: u32,
            source: ACSLocation,
            target: ACSLocation,
            guard: CSIntervalConstraint,
            actions: Vec<CSIntervalAction>,
        ) -> Self {
            Self {
                id,
                source,
                target,
                guard,
                actions,
            }
        }
    }

    impl ACSThresholdAutomaton {
        pub fn to_cs_loc(&self, loc: &Location) -> ACSLocation {
            self.idx_ctx.to_cs_loc(loc)
        }

        pub fn to_cs_var(&self, var: &Variable) -> CSVariable {
            self.idx_ctx.to_cs_var(var)
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{
        collections::{HashMap, HashSet},
        vec,
    };

    use taco_interval_ta::{
        IntervalActionEffect, IntervalConstraint, IntervalTAAction, IntervalTARule,
        builder::IntervalTABuilder, interval::Interval,
    };
    use taco_smt_encoder::SMTSolverBuilder;
    use taco_threshold_automaton::{
        ThresholdAutomaton, VariableConstraint,
        expressions::{
            BooleanExpression, ComparisonOp, IntegerExpression, IsDeclared, Location, Parameter,
            Variable,
        },
        general_threshold_automaton::{
            Action,
            builder::{GeneralThresholdAutomatonBuilder, RuleBuilder},
        },
        lia_threshold_automaton::LIAThresholdAutomaton,
    };

    use crate::acs_threshold_automaton::{
        ACSInterval, ACSLocation, ACSThresholdAutomaton, CSIntervalAction, CSIntervalConstraint,
        CSRule, CSVariable,
        configuration::{ACSIntervalState, ACSTAConfig},
        index_ctx::IndexCtx,
    };

    #[test]
    fn test_from_cs_ta_automaton() {
        let ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_variables([Variable::new("x"), Variable::new("y")])
            .unwrap()
            .with_locations([
                Location::new("l1"),
                Location::new("l2"),
                Location::new("l3"),
            ])
            .unwrap()
            .with_parameter(Parameter::new("n"))
            .unwrap()
            .initialize()
            .with_resilience_condition(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Param(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(3)),
            ))
            .unwrap()
            .with_initial_location_constraints([
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("l2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("l3"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ])
            .unwrap()
            .with_initial_variable_constraints([
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("x"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("y"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ])
            .unwrap()
            .with_rule(
                RuleBuilder::new(0, Location::new("l1"), Location::new("l2"))
                    .with_guard(BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("x"))),
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(2)),
                    ))
                    .with_action(
                        Action::new(
                            Variable::new("x"),
                            IntegerExpression::Const(1)
                                + IntegerExpression::Atom(Variable::new("x")),
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
        let interval_ta = interval_tas.next().unwrap();
        assert!(interval_tas.next().is_none());
        let ta = ACSThresholdAutomaton::from(interval_ta);

        assert!(ta.is_declared(&Parameter::new("n")));
        assert!(ta.is_declared(&Location::new("l1")));
        assert!(ta.is_declared(&Variable::new("y")));

        assert_eq!(
            ta.initial_location_constraints().collect::<HashSet<_>>(),
            HashSet::from([
                &BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("l2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                &BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("l3"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ])
        );
        assert_eq!(
            ta.initial_variable_constraints()
                .map(|c| { c.as_boolean_expr() })
                .collect::<HashSet<_>>(),
            HashSet::from([
                (BooleanExpression::False
                    | (BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("x"))),
                        ComparisonOp::Geq,
                        Box::new(IntegerExpression::Const(0)),
                    ) & BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("x"))),
                        ComparisonOp::Lt,
                        Box::new(IntegerExpression::Const(1)),
                    ))),
                (BooleanExpression::False
                    | (BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("y"))),
                        ComparisonOp::Geq,
                        Box::new(IntegerExpression::Const(0)),
                    ) & BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("y"))),
                        ComparisonOp::Lt,
                        Box::new(IntegerExpression::Const(1)),
                    ))),
            ])
        );
        assert_eq!(
            ta.resilience_conditions().collect::<HashSet<_>>(),
            HashSet::from([
                &BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Param(Parameter::new("n"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(3)),
                ),
                &BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Const(0)),
                    ComparisonOp::Lt,
                    Box::new(IntegerExpression::Const(1)),
                ),
                &BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Const(1)),
                    ComparisonOp::Lt,
                    Box::new(IntegerExpression::Const(2)),
                ),
            ])
        );

        assert_eq!(
            ta.locations().collect::<HashSet<_>>(),
            HashSet::from([&ACSLocation(0), &ACSLocation(1), &ACSLocation(2)])
        );
        assert_eq!(
            ta.variables().collect::<HashSet<_>>(),
            HashSet::from([&CSVariable(0), &CSVariable(1)])
        );
        assert_eq!(ta.name(), "test_ta");
        assert_eq!(
            ta.rules().collect::<HashSet<_>>(),
            HashSet::from([&CSRule {
                id: 0,
                source: ta.idx_ctx.to_cs_loc(&Location::new("l1")),
                target: ta.idx_ctx.to_cs_loc(&Location::new("l2")),
                guard: CSIntervalConstraint::VarGuard(
                    ta.idx_ctx.to_cs_var(&Variable::new("x")),
                    vec![ACSInterval(3)]
                ),
                actions: vec![CSIntervalAction {
                    var: ta.idx_ctx.to_cs_var(&Variable::new("x")),
                    effect: IntervalActionEffect::Inc(1)
                }]
            }])
        );
        assert_eq!(
            ta.get_rule_by_id(0),
            Some(
                &RuleBuilder::new(0, Location::new("l1"), Location::new("l2"))
                    .with_guard(BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("x"))),
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(2)),
                    ))
                    .with_action(
                        Action::new(
                            Variable::new("x"),
                            IntegerExpression::Const(1)
                                + IntegerExpression::Atom(Variable::new("x")),
                        )
                        .unwrap(),
                    )
                    .build()
            )
        );
        assert_eq!(ta.get_rule_by_id(1), None);

        assert_eq!(ta.get_zero_interval(&CSVariable(0)), ACSInterval(0));
        assert_eq!(ta.get_zero_interval(&CSVariable(1)), ACSInterval(0));

        assert!(ta.is_initial_loc(&ta.idx_ctx.to_cs_loc(&Location::new("l1"))));
        assert!(!ta.is_initial_loc(&ta.idx_ctx.to_cs_loc(&Location::new("l2"))));
        assert!(!ta.is_initial_loc(&ta.idx_ctx.to_cs_loc(&Location::new("l3"))));

        assert!(ta.is_initial_interval(&CSVariable(1), &ACSInterval(0)));
        assert!(ta.is_initial_interval(&CSVariable(0), &ACSInterval(0)));
        assert!(!ta.is_initial_interval(&CSVariable(0), &ACSInterval(1)));
        assert!(!ta.is_initial_interval(&CSVariable(1), &ACSInterval(1)));

        assert_eq!(ta.get_zero_interval(&CSVariable(0)), ACSInterval(0));
        assert_eq!(ta.get_zero_interval(&CSVariable(1)), ACSInterval(0));

        assert_eq!(
            ta.get_all_intervals(&ta.idx_ctx.to_cs_var(&Variable::new("x")))
                .collect::<HashSet<_>>(),
            HashSet::from([
                &ACSInterval(0),
                &ACSInterval(1),
                &ACSInterval(2),
                &ACSInterval(3)
            ])
        );
        assert_eq!(
            ta.get_all_intervals(&ta.idx_ctx.to_cs_var(&Variable::new("y")))
                .collect::<HashSet<_>>(),
            HashSet::from([&ACSInterval(0), &ACSInterval(1)])
        );

        assert_eq!(
            ta.get_next_interval(&ta.idx_ctx.to_cs_var(&Variable::new("x")), &ACSInterval(3)),
            None
        );
        assert_eq!(
            ta.get_next_interval(&ta.idx_ctx.to_cs_var(&Variable::new("x")), &ACSInterval(1)),
            Some(ACSInterval(2))
        );

        assert_eq!(
            ta.get_prev_interval(&ta.idx_ctx.to_cs_var(&Variable::new("x")), &ACSInterval(2)),
            Some(ACSInterval(1))
        );
        assert_eq!(
            ta.get_prev_interval(&ta.idx_ctx.to_cs_var(&Variable::new("x")), &ACSInterval(0)),
            None,
        );
    }

    #[test]
    fn test_cs_interval_constr_from_interval_constraint() {
        // Test translation of True constraint
        let index_ctx = IndexCtx::new_mock(
            HashMap::new(),
            HashMap::from([(Variable::new("x"), CSVariable(0))]),
            vec![HashMap::from([(
                Interval::new_constant(0, 1),
                ACSInterval(0),
            )])],
        );
        let ic = IntervalConstraint::True;
        let cs_ic = CSIntervalConstraint::from_interval_constr(&index_ctx, &ic);
        assert_eq!(cs_ic, CSIntervalConstraint::True);

        // Test translation of False constraint
        let ic = IntervalConstraint::False;
        let cs_ic = CSIntervalConstraint::from_interval_constr(&index_ctx, &ic);
        assert_eq!(cs_ic, CSIntervalConstraint::False);

        // Test translation of SingleVarIntervalConstr
        let ic = IntervalConstraint::SingleVarIntervalConstr(
            Variable::new("x"),
            vec![Interval::new_constant(0, 1)],
        );
        let cs_ic = CSIntervalConstraint::from_interval_constr(&index_ctx, &ic);
        assert_eq!(
            cs_ic,
            CSIntervalConstraint::VarGuard(CSVariable(0), vec![ACSInterval(0)])
        );

        // Test translation of Conj
        let ic = IntervalConstraint::Conj(
            Box::new(IntervalConstraint::True),
            Box::new(IntervalConstraint::False),
        );
        let cs_ic = CSIntervalConstraint::from_interval_constr(&index_ctx, &ic);
        assert_eq!(
            cs_ic,
            CSIntervalConstraint::Conj(
                Box::new(CSIntervalConstraint::True),
                Box::new(CSIntervalConstraint::False)
            )
        );

        // Test translation of Disj
        let ic = IntervalConstraint::Disj(
            Box::new(IntervalConstraint::False),
            Box::new(IntervalConstraint::True),
        );
        let cs_ic = CSIntervalConstraint::from_interval_constr(&index_ctx, &ic);
        assert_eq!(
            cs_ic,
            CSIntervalConstraint::Disj(
                Box::new(CSIntervalConstraint::False),
                Box::new(CSIntervalConstraint::True)
            )
        );

        // Test translation of nested constraints
        let ic = IntervalConstraint::Disj(
            Box::new(IntervalConstraint::Conj(
                Box::new(IntervalConstraint::SingleVarIntervalConstr(
                    Variable::new("x"),
                    vec![Interval::new_constant(0, 1)],
                )),
                Box::new(IntervalConstraint::True),
            )),
            Box::new(IntervalConstraint::False),
        );
        let cs_ic = CSIntervalConstraint::from_interval_constr(&index_ctx, &ic);
        assert_eq!(
            cs_ic,
            CSIntervalConstraint::Disj(
                Box::new(CSIntervalConstraint::Conj(
                    Box::new(CSIntervalConstraint::VarGuard(
                        CSVariable(0),
                        vec![ACSInterval(0)]
                    )),
                    Box::new(CSIntervalConstraint::True)
                )),
                Box::new(CSIntervalConstraint::False)
            )
        );
    }

    #[test]
    fn test_cs_interval_constraint_is_sat() {
        let interval_state = ACSIntervalState::new_mock_from_vec(vec![ACSInterval(1)]);

        let ic = CSIntervalConstraint::True;
        assert!(ic.is_satisfied(&interval_state));

        // Test False constraint
        let ic = CSIntervalConstraint::False;
        assert!(!ic.is_satisfied(&interval_state));

        // Test VarGuard with matching interval
        let ic = CSIntervalConstraint::VarGuard(CSVariable(0), vec![ACSInterval(1)]);
        assert!(ic.is_satisfied(&interval_state));

        // Test VarGuard with non-matching interval
        let ic = CSIntervalConstraint::VarGuard(CSVariable(0), vec![ACSInterval(2)]);
        assert!(!ic.is_satisfied(&interval_state));

        // Test Conj (True && True)
        let ic = CSIntervalConstraint::Conj(
            Box::new(CSIntervalConstraint::True),
            Box::new(CSIntervalConstraint::True),
        );
        assert!(ic.is_satisfied(&interval_state));

        // Test Conj (True && False)
        let ic = CSIntervalConstraint::Conj(
            Box::new(CSIntervalConstraint::True),
            Box::new(CSIntervalConstraint::False),
        );
        assert!(!ic.is_satisfied(&interval_state));

        // Test Disj (False || True)
        let ic = CSIntervalConstraint::Disj(
            Box::new(CSIntervalConstraint::False),
            Box::new(CSIntervalConstraint::True),
        );
        assert!(ic.is_satisfied(&interval_state));

        // Test Disj (False || False)
        let ic = CSIntervalConstraint::Disj(
            Box::new(CSIntervalConstraint::False),
            Box::new(CSIntervalConstraint::False),
        );
        assert!(!ic.is_satisfied(&interval_state));

        // Test nested constraints: (VarGuard(0, [1]) && True) || False
        let ic = CSIntervalConstraint::Disj(
            Box::new(CSIntervalConstraint::Conj(
                Box::new(CSIntervalConstraint::VarGuard(
                    CSVariable(0),
                    vec![ACSInterval(1)],
                )),
                Box::new(CSIntervalConstraint::True),
            )),
            Box::new(CSIntervalConstraint::False),
        );
        assert!(ic.is_satisfied(&interval_state));

        // Test nested constraints: (VarGuard(0, [2]) && True) || False
        let ic = CSIntervalConstraint::Disj(
            Box::new(CSIntervalConstraint::Conj(
                Box::new(CSIntervalConstraint::VarGuard(
                    CSVariable(0),
                    vec![ACSInterval(2)],
                )),
                Box::new(CSIntervalConstraint::True),
            )),
            Box::new(CSIntervalConstraint::False),
        );
        assert!(!ic.is_satisfied(&interval_state));
    }

    #[test]
    fn test_cs_interval_action_from_interval_action() {
        let index_ctx = IndexCtx::new_mock(
            HashMap::new(),
            HashMap::from([(Variable::new("x"), CSVariable(0))]),
            vec![HashMap::new()],
        );

        // Test with Inc effect
        let interval_action =
            IntervalTAAction::new(Variable::new("x"), IntervalActionEffect::Inc(5));

        let cs_action = CSIntervalAction::from_interval_action(&index_ctx, &interval_action);
        assert_eq!(cs_action.variable(), &CSVariable(0));
        assert_eq!(cs_action.effect(), &IntervalActionEffect::Inc(5));

        // Test with Reset effect
        let interval_action_reset =
            IntervalTAAction::new(Variable::new("x"), IntervalActionEffect::Reset);
        let cs_action_reset =
            CSIntervalAction::from_interval_action(&index_ctx, &interval_action_reset);
        assert_eq!(cs_action_reset.variable(), &CSVariable(0));
        assert_eq!(cs_action_reset.effect(), &IntervalActionEffect::Reset);

        // Test with Dec effect
        let interval_action_dec =
            IntervalTAAction::new(Variable::new("x"), IntervalActionEffect::Dec(2));
        let cs_action_dec =
            CSIntervalAction::from_interval_action(&index_ctx, &interval_action_dec);
        assert_eq!(cs_action_dec.variable(), &CSVariable(0));
        assert_eq!(cs_action_dec.effect(), &IntervalActionEffect::Dec(2));
    }

    #[test]
    fn test_getters_csrule() {
        let rule = CSRule {
            id: 0,
            source: ACSLocation(1),
            target: ACSLocation(2),
            guard: CSIntervalConstraint::True,
            actions: vec![CSIntervalAction {
                var: CSVariable(0),
                effect: IntervalActionEffect::Inc(43),
            }],
        };

        assert_eq!(rule.id(), 0);
        assert_eq!(rule.target(), &ACSLocation(2));
        assert_eq!(rule.source(), &ACSLocation(1));
        assert_eq!(
            rule.actions().collect::<Vec<_>>(),
            vec![&CSIntervalAction {
                var: CSVariable(0),
                effect: IntervalActionEffect::Inc(43),
            }]
        );
        assert_eq!(rule.guard(), &CSIntervalConstraint::True);
    }

    #[test]
    fn test_csrule_is_enabled() {
        let rule = CSRule {
            id: 0,
            source: ACSLocation(1),
            target: ACSLocation(2),
            guard: CSIntervalConstraint::True,
            actions: vec![CSIntervalAction {
                var: CSVariable(0),
                effect: IntervalActionEffect::Inc(43),
            }],
        };
        let cfg = ACSTAConfig::new_mock_from_vecs(vec![0, 1, 2], vec![ACSInterval(0)]);
        assert!(rule.is_enabled(&cfg));

        let rule = CSRule {
            id: 0,
            source: ACSLocation(1),
            target: ACSLocation(2),
            guard: CSIntervalConstraint::True,
            actions: vec![CSIntervalAction {
                var: CSVariable(0),
                effect: IntervalActionEffect::Inc(43),
            }],
        };
        let cfg = ACSTAConfig::new_mock_from_vecs(vec![0, 0, 2], vec![ACSInterval(0)]);
        assert!(!rule.is_enabled(&cfg));

        let rule = CSRule {
            id: 0,
            source: ACSLocation(1),
            target: ACSLocation(2),
            guard: CSIntervalConstraint::False,
            actions: vec![CSIntervalAction {
                var: CSVariable(0),
                effect: IntervalActionEffect::Inc(43),
            }],
        };
        let cfg = ACSTAConfig::new_mock_from_vecs(vec![2, 2, 2], vec![ACSInterval(0)]);
        assert!(!rule.is_enabled(&cfg));

        let rule = CSRule {
            id: 0,
            source: ACSLocation(1),
            target: ACSLocation(2),
            guard: CSIntervalConstraint::VarGuard(CSVariable(0), vec![ACSInterval(1)]),
            actions: vec![CSIntervalAction {
                var: CSVariable(0),
                effect: IntervalActionEffect::Inc(43),
            }],
        };
        let cfg = ACSTAConfig::new_mock_from_vecs(vec![2, 2, 2], vec![ACSInterval(1)]);
        assert!(rule.is_enabled(&cfg));

        let rule = CSRule {
            id: 0,
            source: ACSLocation(1),
            target: ACSLocation(2),
            guard: CSIntervalConstraint::VarGuard(CSVariable(0), vec![ACSInterval(2)]),
            actions: vec![CSIntervalAction {
                var: CSVariable(0),
                effect: IntervalActionEffect::Inc(43),
            }],
        };
        let cfg = ACSTAConfig::new_mock_from_vecs(vec![2, 2, 2], vec![ACSInterval(1)]);
        assert!(!rule.is_enabled(&cfg));
    }

    #[test]
    fn test_csrule_from_interval_rule() {
        let index_ctx = IndexCtx::new_mock(
            HashMap::from([
                (Location::new("loc0"), ACSLocation(0)),
                (Location::new("loc1"), ACSLocation(1)),
            ]),
            HashMap::from([(Variable::new("var0"), CSVariable(0))]),
            vec![HashMap::from([(
                Interval::new_constant(0, 1),
                ACSInterval(0),
            )])],
        );

        let interval_rule = IntervalTARule::new(
            0,
            Location::new("loc0"),
            Location::new("loc1"),
            IntervalConstraint::SingleVarIntervalConstr(
                Variable::new("var0"),
                vec![Interval::new_constant(0, 1)],
            ),
            vec![IntervalTAAction::new(
                Variable::new("var0"),
                IntervalActionEffect::Inc(1),
            )],
        );

        let expected_rule = CSRule {
            id: 0,
            source: ACSLocation(0),
            target: ACSLocation(1),
            guard: CSIntervalConstraint::VarGuard(CSVariable(0), vec![ACSInterval(0)]),
            actions: vec![CSIntervalAction {
                var: CSVariable(0),
                effect: IntervalActionEffect::Inc(1),
            }],
        };

        assert_eq!(
            CSRule::from_interval_rule(&index_ctx, &interval_rule),
            expected_rule
        )
    }
}
