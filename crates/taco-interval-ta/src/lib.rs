//! Threshold Automaton with applied interval abstraction
//!
//! This crate defines `IntervalThresholdAutomaton` which is a type representing
//! a threshold automaton to which interval abstraction has been applied. Guards
//! are abstracted to sets of symbolic intervals, depending on the interval
//! order that is used for the automaton.
//!
//! This crate also provides the types for defining and working with intervals
//! and implements an ordering mechanism for intervals.

use builder::{IntervalTABuilder, static_interval_order::StaticIntervalOrder};
use interval::{Interval, IntervalOrderError, IntervalOrderFor};
use log::warn;
use taco_display_utils::{
    display_iterator_stable_order, indent_all, join_iterator, join_iterator_and_add_back,
};
use taco_model_checker::{ModelCheckerContext, TASpecification, TATrait};
use taco_smt_encoder::ProvidesSMTSolverBuilder;
use taco_threshold_automaton::expressions::{And, BooleanConnective, IsDeclared, Or};
use taco_threshold_automaton::general_threshold_automaton::{
    Action, GeneralThresholdAutomaton, Rule, UpdateExpression,
};
use taco_threshold_automaton::lia_threshold_automaton::integer_thresholds::WeightedSum;
use taco_threshold_automaton::lia_threshold_automaton::{
    LIARule, LIATransformationError, LIAVariableConstraint,
};

use taco_threshold_automaton::{
    ActionDefinition, LocationConstraint, RuleDefinition, ThresholdAutomaton, VariableConstraint,
    impl_bitand, impl_bitor,
};
use taco_threshold_automaton::{
    expressions::{BooleanExpression, Location, Parameter, Variable},
    lia_threshold_automaton::LIAThresholdAutomaton,
};

use std::collections::HashSet;
use std::error;
use std::{
    collections::HashMap,
    fmt::{self, Debug, Display},
    hash,
};

pub mod builder;
pub mod interval;

/// Threshold automaton with guards abstracted to sets of intervals
///
/// A threshold automaton where a specific order on intervals is defined and
/// the guards are abstracted to sets of intervals in which they are enabled.
#[derive(Debug, Clone)]
pub struct IntervalThresholdAutomaton {
    /// Underlying linear integer arithmetic threshold automaton
    lia_ta: LIAThresholdAutomaton,
    /// Initial variable constraints as intervals
    initial_variable_constraints: Vec<IntervalConstraint>,
    /// Abstract rules of the threshold automaton
    rules: Vec<IntervalTARule>,
    /// Current interval order
    order: StaticIntervalOrder,
    /// Order expression
    order_expr: Vec<BooleanExpression<Parameter>>,
}

impl IntervalThresholdAutomaton {
    /// Get the initial interval for variable `var`
    pub fn get_initial_interval<'a>(&'a self, var: &Variable) -> Vec<&'a Interval> {
        let intervals_for_var = self
            .order
            .get_all_intervals_of_t(var)
            .unwrap_or_else(|_| panic!("Failed to get intervals of variable {}", var))
            .iter()
            .collect();

        self.initial_variable_constraints
            .iter()
            .fold(intervals_for_var, |acc, constr| {
                constr.get_enabled_intervals(var, acc)
            })
    }

    /// Get the zero interval for variable `var`
    pub fn get_zero_interval<'a>(&'a self, var: &Variable) -> &'a Interval {
        self.order
            .get_zero_interval(var)
            .unwrap_or_else(|_| panic!("Failed to get zero interval for variable {}", var))
    }

    /// Get intervals for variable `var`
    pub fn get_intervals(&self, var: &Variable) -> &Vec<Interval> {
        self.order
            .get_all_intervals_of_t(var)
            .unwrap_or_else(|_| panic!("Failed to get intervals for variable {var}"))
    }

    /// Get the previous interval of `i` for variable `var`
    ///
    /// Returns `None` if `i` is the first interval
    pub fn get_previous_interval(&self, var: &Variable, i: &Interval) -> Option<&Interval> {
        self.order
            .get_previous_interval(var, i)
            .unwrap_or_else(|_| panic!("Failed to get previous interval for variable {var}"))
    }

    /// Get the next interval of `i` for variable `var`
    ///
    /// Returns `None` if `i` is the open interval
    pub fn get_next_interval(&self, var: &Variable, i: &Interval) -> Option<&Interval> {
        self.order
            .get_next_interval(var, i)
            .unwrap_or_else(|_| panic!("Failed to get next interval for variable {var}"))
    }

    /// Get the corresponding concrete rule for a given abstract rule
    pub fn get_derived_rule(&self, abstract_rule: &IntervalTARule) -> &Rule {
        self.lia_ta
            .get_ta()
            .rules()
            .find(|rule| {
                rule.id() == abstract_rule.id()
                    && rule.source() == abstract_rule.source()
                    && rule.target() == abstract_rule.target()
            })
            .unwrap()
    }

    /// Translate a [LIAVariableConstraint] into an [IntervalConstraint] in the
    /// interval order of the automaton
    ///
    /// This function will return an error if the constraint contains a
    /// threshold that was not present when the interval order was constructed
    pub fn get_interval_constraint(
        &self,
        constr: &LIAVariableConstraint,
    ) -> Result<IntervalConstraint, IntervalConstraintConstructionError> {
        IntervalConstraint::from_lia_constr(constr, &self.order)
    }

    /// Get the intervals in which the interval constraint is enabled
    pub fn get_enabled_intervals<'a>(
        &'a self,
        constr: &'a IntervalConstraint,
        var: &Variable,
    ) -> impl Iterator<Item = &'a Interval> {
        // TODO: adjust when multivar

        constr
            .get_enabled_intervals(var, self.get_intervals(var).iter().collect())
            .into_iter()
    }

    /// Get all variables for which the interval constraint actually
    /// constrains the interval a variable can be in
    pub fn get_variables_constrained(&self, constr: &IntervalConstraint) -> Vec<&Variable> {
        self.variables()
            .filter(|var| {
                self.get_enabled_intervals(constr, var)
                    .collect::<HashSet<_>>()
                    != self.get_intervals(var).iter().collect::<HashSet<_>>()
            })
            .collect()
    }

    /// Get the underlying threshold automaton
    pub fn get_ta(&self) -> &GeneralThresholdAutomaton {
        self.lia_ta.get_ta()
    }

    /// Get the interval order for a specific variable
    ///
    /// Returns all intervals for variable `var` in the interval order of the
    /// automaton
    pub fn get_ordered_intervals(
        &self,
        var: &Variable,
    ) -> Result<&Vec<Interval>, IntervalOrderError<Variable>> {
        let intervals = self
            .order
            .single_var_order()
            .get(var)
            .ok_or_else(|| IntervalOrderError::VariableNotFound { var: var.clone() })?;
        Ok(intervals)
    }

    /// TODO: Remove when interval order is ready
    pub fn get_helper_vars_for_sumvars(&self) -> &HashMap<Variable, WeightedSum<Variable>> {
        self.lia_ta.get_replacement_vars_for_sumvars()
    }
}

impl ThresholdAutomaton for IntervalThresholdAutomaton {
    type Rule = IntervalTARule;
    type InitialVariableConstraintType = IntervalConstraint;

    fn name(&self) -> &str {
        self.lia_ta.name()
    }

    fn parameters(&self) -> impl Iterator<Item = &Parameter> {
        self.lia_ta.parameters()
    }

    fn resilience_conditions(&self) -> impl Iterator<Item = &BooleanExpression<Parameter>> {
        self.lia_ta
            .resilience_conditions()
            .chain(self.order_expr.iter())
    }

    fn variables(&self) -> impl Iterator<Item = &Variable> {
        self.lia_ta.variables()
    }

    fn locations(&self) -> impl Iterator<Item = &Location> {
        self.lia_ta.locations()
    }

    fn can_be_initial_location(&self, location: &Location) -> bool {
        self.lia_ta.can_be_initial_location(location)
    }

    fn rules(&self) -> impl Iterator<Item = &Self::Rule> {
        self.rules.iter()
    }

    fn incoming_rules(&self, location: &Location) -> impl Iterator<Item = &Self::Rule> {
        self.rules
            .iter()
            .filter(move |rule| rule.target() == location)
    }

    fn outgoing_rules(&self, location: &Location) -> impl Iterator<Item = &Self::Rule> {
        self.rules
            .iter()
            .filter(move |rule| rule.source() == location)
    }

    fn initial_location_constraints(&self) -> impl Iterator<Item = &LocationConstraint> {
        self.lia_ta.initial_location_constraints()
    }

    fn initial_variable_constraints(&self) -> impl Iterator<Item = &IntervalConstraint> {
        self.initial_variable_constraints.iter()
    }
}

/// Trait marking types that can be abstracted by intervals
///
/// This trait is implemented by types that have a set of intervals associated
/// with them, e.g., `Variable` and `WeightedSum<Variable>` that appear in
/// guards of the automaton.
pub trait HasAssociatedIntervals: hash::Hash + Eq + Display + Debug + Clone {}

/// Mark `Variable` as having associated intervals, as they appear in guards
/// `SingleVariableGuard`s
impl HasAssociatedIntervals for Variable {}

/// Mark `WeightedSum<Variable>` as having associated intervals as they appear
/// in guards `MultiVariableGuard`s
impl HasAssociatedIntervals for WeightedSum<Variable> {}

impl fmt::Display for IntervalThresholdAutomaton {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let order = self.order.to_string();

        let variables = format!(
            "shared {};",
            display_iterator_stable_order(self.variables())
        );

        let parameters = format!(
            "parameters {};",
            display_iterator_stable_order(self.parameters())
        );

        let rc = format!(
            "assumptions ({}) {{\n{}}}",
            self.resilience_conditions().count(),
            indent_all(join_iterator_and_add_back(
                self.resilience_conditions(),
                ";\n"
            ))
        );

        let mut location_str = String::new();
        let mut locations = self.locations().collect::<Vec<_>>();
        locations.sort();

        for (i, loc) in locations.into_iter().enumerate() {
            location_str += &format!("{loc}:[{i}];\n");
        }
        let locations = format!(
            "locations ({}) {{\n{}}}",
            self.locations().count(),
            indent_all(location_str)
        );

        let initial_cond = format!(
            "inits ({}) {{\n{}}}",
            self.initial_location_constraints().count()
                + self.initial_variable_constraints().count(),
            indent_all(
                join_iterator_and_add_back(self.initial_location_constraints(), ";\n")
                    + &join_iterator_and_add_back(self.initial_variable_constraints(), ";\n")
            )
        );

        let mut sorted_rules_by_id = self.rules().collect::<Vec<_>>();
        sorted_rules_by_id.sort_by_key(|r| &r.id);
        let rules = format!(
            "rules ({}) {{\n{}}}",
            self.rules().count(),
            indent_all(join_iterator_and_add_back(
                sorted_rules_by_id.into_iter(),
                ";\n"
            ))
        );

        let ta_body = format!(
            "{order}\n\n{variables}\n\n{parameters}\n\n{rc}\n\n{locations}\n\n{initial_cond}\n\n{rules}"
        );

        write!(
            f,
            "thresholdAutomaton {} {{\n{}\n}}\n",
            self.name(),
            indent_all(ta_body)
        )
    }
}

impl IsDeclared<Parameter> for IntervalThresholdAutomaton {
    fn is_declared(&self, obj: &Parameter) -> bool {
        self.lia_ta.is_declared(obj)
    }
}

impl IsDeclared<Location> for IntervalThresholdAutomaton {
    fn is_declared(&self, obj: &Location) -> bool {
        self.lia_ta.is_declared(obj)
    }
}

impl IsDeclared<Variable> for IntervalThresholdAutomaton {
    fn is_declared(&self, obj: &Variable) -> bool {
        self.lia_ta.is_declared(obj)
    }
}

impl<C: ModelCheckerContext + ProvidesSMTSolverBuilder, SC: TASpecification> TATrait<C, SC>
    for IntervalThresholdAutomaton
{
    type TransformationError = IntervalTATransformationError;

    fn try_from_general_ta(
        ta: GeneralThresholdAutomaton,
        ctx: &C,
        spec_ctx: &SC,
    ) -> Result<Vec<Self>, Self::TransformationError> {
        let solver_builder = ctx.get_solver_builder();

        let lta = LIAThresholdAutomaton::try_from(ta);
        if let Err(lta_err) = lta {
            return Err(IntervalTATransformationError::LIATransformationError(
                Box::new(lta_err),
            ));
        }

        // TODO: remove this preprocessing when sum of variables is implemented
        let lta = lta.unwrap().into_ta_without_sum_vars();

        let target_constrs = spec_ctx.var_constraint().into_iter().cloned().collect();

        let builder = IntervalTABuilder::new(lta, solver_builder, target_constrs);

        let itas = builder.build()?;
        Ok(itas.collect())
    }
}

/// Interval abstracted rule
///
/// Rule of the abstract threshold automaton with an interval guard
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct IntervalTARule {
    /// Id assigned to the rule in the specification
    id: u32,
    /// Source location of the rule
    source: Location,
    /// Target location of the rule
    target: Location,
    /// Guard of the rule
    guard: IntervalConstraint,
    /// Effect of the rule
    actions: Vec<IntervalTAAction>,
}

impl IntervalTARule {
    /// Creates a new abstract Rule for testing purposes
    pub fn new(
        id: u32,
        source: Location,
        target: Location,
        guard: IntervalConstraint,
        effect: Vec<IntervalTAAction>,
    ) -> IntervalTARule {
        IntervalTARule {
            id,
            source,
            target,
            guard,
            actions: effect,
        }
    }

    /// Check if the rule updates the given variable
    pub fn updates_variable(&self, var: &Variable) -> bool {
        self.actions().any(|action| action.variable() == var)
    }

    /// Returns the guard of the rule
    pub fn get_guard(&self) -> &IntervalConstraint {
        &self.guard
    }

    /// Check whether the rule is enabled in the given state
    pub fn is_enabled(
        &self,
        state: &IntervalState<Variable>,
    ) -> Result<bool, IntervalOrderError<Variable>> {
        self.guard.is_enabled(state)
    }

    /// Derive an interval rule from a rule of a linear integer arithmetic rule
    /// given a fixed order
    fn from_lia_rule<O: IntervalOrderFor<Variable> + IntervalOrderFor<WeightedSum<Variable>>>(
        rule: &LIARule,
        order: &O,
    ) -> IntervalTARule {
        let guard = IntervalConstraint::from_lia_constr(rule.guard(), order)
            .expect("Failed to derive guard interval constraint");

        let actions = rule.actions().map(|action| action.clone().into()).collect();

        IntervalTARule::new(
            rule.id(),
            rule.source().clone(),
            rule.target().clone(),
            guard,
            actions,
        )
    }
}

impl RuleDefinition for IntervalTARule {
    type Action = IntervalTAAction;
    type Guard = IntervalConstraint;

    fn id(&self) -> u32 {
        self.id
    }

    fn source(&self) -> &Location {
        &self.source
    }

    fn target(&self) -> &Location {
        &self.target
    }

    fn guard(&self) -> &Self::Guard {
        &self.guard
    }

    fn actions(&self) -> impl Iterator<Item = &Self::Action> {
        self.actions.iter()
    }
}

impl Display for IntervalTARule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let rule_body = indent_all(format!(
            "when ( {} )\ndo {{ {} }}",
            self.guard,
            join_iterator(self.actions.iter(), "; ")
        ));

        write!(
            f,
            "{}: {} -> {}\n{}",
            self.id, self.source, self.target, rule_body
        )
    }
}

impl Display for IntervalTAAction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", self.variable, self.effect)
    }
}

impl Display for IntervalActionEffect {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IntervalActionEffect::Inc(_i) => write!(f, "++"),
            IntervalActionEffect::Dec(_i) => write!(f, "--"),
            IntervalActionEffect::Reset => write!(f, "= 0"),
        }
    }
}

impl Display for IntervalConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IntervalConstraint::True => write!(f, "true"),
            IntervalConstraint::False => write!(f, "false"),
            IntervalConstraint::Conj(g1, g2) => write!(f, "{g1} && {g2}"),
            IntervalConstraint::Disj(g1, g2) => write!(f, "{g1} || {g2}"),
            IntervalConstraint::SingleVarIntervalConstr(var, intervals) => {
                write!(
                    f,
                    "{} ∈ {{ {} }}",
                    var,
                    join_iterator(intervals.iter(), ", ")
                )
            }
            IntervalConstraint::MultiVarIntervalConstr(weighted_sum, intervals) => {
                write!(
                    f,
                    "{}  ∈ {{ {} }}",
                    weighted_sum,
                    join_iterator(intervals.iter(), ", ")
                )
            }
        }
    }
}

/// Action describing the effect of an action on an interval
///
/// The action updates the interval of a variable
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct IntervalTAAction {
    /// Variable to be updated
    variable: Variable,
    /// Effect of the action
    effect: IntervalActionEffect,
}

impl IntervalTAAction {
    /// Creates a new interval action
    pub fn new(variable: Variable, effect: IntervalActionEffect) -> IntervalTAAction {
        IntervalTAAction { variable, effect }
    }

    /// Returns the effect of the action
    pub fn effect(&self) -> &IntervalActionEffect {
        &self.effect
    }
}

impl From<Action> for IntervalTAAction {
    fn from(val: Action) -> Self {
        let variable = val.variable().clone();
        let effect = match val.update() {
            UpdateExpression::Inc(i) => IntervalActionEffect::Inc(*i),
            UpdateExpression::Dec(d) => IntervalActionEffect::Dec(*d),
            UpdateExpression::Reset => IntervalActionEffect::Reset,
            UpdateExpression::Unchanged => unreachable!("Should have been removed"),
        };

        IntervalTAAction::new(variable, effect)
    }
}

/// Describes the effect of an action to the interval
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum IntervalActionEffect {
    /// Increment
    Inc(u32),
    /// Decrement
    Dec(u32),
    /// Reset to the zero interval
    Reset,
}

impl ActionDefinition for IntervalTAAction {
    fn variable(&self) -> &Variable {
        &self.variable
    }

    fn is_unchanged(&self) -> bool {
        false
    }

    fn is_reset(&self) -> bool {
        matches!(self.effect, IntervalActionEffect::Reset)
    }

    fn is_increment(&self) -> bool {
        matches!(self.effect, IntervalActionEffect::Inc(_))
    }

    fn is_decrement(&self) -> bool {
        matches!(self.effect, IntervalActionEffect::Dec(_))
    }
}

/// Interval guard constraining the interval of evaluation of a variable
/// or a sum of variables
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum IntervalConstraint {
    /// Guard is always enabled
    True,
    /// Guard is always disabled
    False,
    /// Conjunction of interval guard
    Conj(Box<IntervalConstraint>, Box<IntervalConstraint>),
    /// Disjunction of interval guard
    Disj(Box<IntervalConstraint>, Box<IntervalConstraint>),
    /// Interval guard over a single variable
    ///
    /// The guard is enabled if the variable is in one of the intervals.
    SingleVarIntervalConstr(Variable, Vec<Interval>),
    /// Interval guard over a sum of variables
    ///
    /// The guard is enabled if the sum of variables is in one of the intervals.
    MultiVarIntervalConstr(WeightedSum<Variable>, Vec<Interval>),
}

/// Interval state for a type `T`
///
/// This struct assigns an interval to each element of type `T`. It can be used
/// to track the abstract state, i.e., the current interval in which `T`
/// currently used.
///
/// On this abstract state, one can check for example whether a guard is enabled.
pub struct IntervalState<T: HasAssociatedIntervals> {
    // map t to its current interval
    t_to_interval: HashMap<T, Interval>,
}

impl IntervalConstraint {
    /// Check if the guard is enabled in the given state
    pub fn is_enabled(
        &self,
        state: &IntervalState<Variable>,
    ) -> Result<bool, IntervalOrderError<Variable>> {
        match self {
            IntervalConstraint::True => Ok(true),
            IntervalConstraint::False => Ok(false),
            IntervalConstraint::Conj(g1, g2) => Ok(g1.is_enabled(state)? && g2.is_enabled(state)?),
            IntervalConstraint::Disj(g1, g2) => Ok(g1.is_enabled(state)? || g2.is_enabled(state)?),
            IntervalConstraint::SingleVarIntervalConstr(var, intervals) => {
                let interval = state
                    .t_to_interval
                    .get(var)
                    .ok_or_else(|| IntervalOrderError::VariableNotFound { var: var.clone() })?;

                Ok(intervals.contains(interval))
            }
            IntervalConstraint::MultiVarIntervalConstr(_multivar, _intervals) => {
                todo!()
            }
        }
    }

    /// Derive an interval guard from a guard of a linear integer arithmetic
    /// guard under the current interval order
    fn from_lia_constr<S: IntervalOrderFor<Variable> + IntervalOrderFor<WeightedSum<Variable>>>(
        guard: &LIAVariableConstraint,
        order: &S,
    ) -> Result<Self, IntervalConstraintConstructionError> {
        match guard {
            LIAVariableConstraint::True => Ok(IntervalConstraint::True),
            LIAVariableConstraint::False => Ok(IntervalConstraint::False),
            LIAVariableConstraint::ComparisonConstraint(_) => {
                unreachable!("Comparison guards not supported by this algorithm")
            }
            LIAVariableConstraint::SingleVarConstraint(g) => {
                let enabled_intervals = order.compute_enabled_intervals_of_threshold(
                    g.get_atom(),
                    g.get_threshold_constraint(),
                )?;

                // simplify the expressions
                if enabled_intervals.is_empty() {
                    return Ok(IntervalConstraint::False);
                }

                // simplify the expressions
                if order
                    .get_all_intervals_of_t(g.get_atom())?
                    .iter()
                    .all(|i| enabled_intervals.contains(i))
                {
                    return Ok(IntervalConstraint::True);
                }

                Ok(IntervalConstraint::SingleVarIntervalConstr(
                    g.get_atom().clone(),
                    enabled_intervals,
                ))
            }
            LIAVariableConstraint::SumVarConstraint(g) => {
                Ok(IntervalConstraint::MultiVarIntervalConstr(
                    g.get_atoms().clone(),
                    order
                        .compute_enabled_intervals_of_threshold(
                            g.get_atoms(),
                            g.get_threshold_constraint(),
                        )
                        .unwrap(),
                ))
            }
            LIAVariableConstraint::BinaryGuard(lhs, con, rhs) => {
                let lhs_guard = Self::from_lia_constr(lhs, order)?;
                let rhs_guard = Self::from_lia_constr(rhs, order)?;

                match con {
                    BooleanConnective::And => {
                        // simplify the expressions
                        if lhs_guard == IntervalConstraint::True {
                            return Ok(rhs_guard);
                        }
                        // simplify the expressions
                        if rhs_guard == IntervalConstraint::True {
                            return Ok(lhs_guard);
                        }

                        Ok(IntervalConstraint::Conj(
                            Box::new(lhs_guard),
                            Box::new(rhs_guard),
                        ))
                    }
                    BooleanConnective::Or => {
                        // simplify the expressions
                        if lhs_guard == IntervalConstraint::False {
                            return Ok(rhs_guard);
                        }
                        // simplify the expressions
                        if rhs_guard == IntervalConstraint::False {
                            return Ok(lhs_guard);
                        }

                        Ok(IntervalConstraint::Disj(
                            Box::new(lhs_guard),
                            Box::new(rhs_guard),
                        ))
                    }
                }
            }
        }
    }

    /// Get the the set of intervals for which the constraint `self` is
    /// satisfied for variable `var`
    ///
    /// This function requires `intervals_of_var` to be the set of all intervals
    /// for `var` in the automaton. (Which can be obtained from the interval
    /// order)
    fn get_enabled_intervals<'a>(
        &'a self,
        var: &Variable,
        mut intervals_of_var: Vec<&'a Interval>,
    ) -> Vec<&'a Interval> {
        match self {
            IntervalConstraint::True => intervals_of_var,
            IntervalConstraint::False => Vec::new(),
            IntervalConstraint::Conj(lhs, rhs) => {
                let lhs_intervals = lhs.get_enabled_intervals(var, intervals_of_var);
                rhs.get_enabled_intervals(var, lhs_intervals)
            }
            IntervalConstraint::Disj(lhs, rhs) => {
                let mut lhs_intervals = lhs.get_enabled_intervals(var, intervals_of_var.clone());
                let mut rhs_intervals = rhs.get_enabled_intervals(var, intervals_of_var);

                rhs_intervals.retain(|i| !lhs_intervals.contains(i));
                lhs_intervals.extend(rhs_intervals);

                lhs_intervals
            }
            IntervalConstraint::SingleVarIntervalConstr(variable, intervals) => {
                if variable == var {
                    intervals_of_var.retain(|i| intervals.contains(i));
                }
                intervals_of_var
            }
            IntervalConstraint::MultiVarIntervalConstr(weighted_sum, _intervals) => {
                // FIXME: Implement the interval arithmetic
                if weighted_sum.contains(var) {
                    warn!(
                        "Interval constraint over a sum of variables not fully implemented ! Tried to get constraints for variable {var}"
                    );
                }

                intervals_of_var
            }
        }
    }
}

impl And for IntervalConstraint {
    fn and(self, other: Self) -> Self {
        IntervalConstraint::Conj(Box::new(self), Box::new(other))
    }
}
impl_bitand!(IntervalConstraint);

impl Or for IntervalConstraint {
    fn or(self, other: Self) -> Self {
        IntervalConstraint::Disj(Box::new(self), Box::new(other))
    }
}
impl_bitor!(IntervalConstraint);

#[derive(Debug, Clone, PartialEq)]
/// Error that can occur during the construction of an [IntervalConstraint]
pub enum IntervalConstraintConstructionError {
    /// Error while attempting to translate a constraint over a single variable
    VarError(IntervalOrderError<Variable>),
    /// Error while attempting to translate a constraint over the sum of variables
    SumVarError(IntervalOrderError<WeightedSum<Variable>>),
}

impl error::Error for IntervalConstraintConstructionError {}

impl fmt::Display for IntervalConstraintConstructionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IntervalConstraintConstructionError::VarError(err) => {
                write!(f, "Error while constructing an IntervalConstraint: {err}")
            }
            IntervalConstraintConstructionError::SumVarError(err) => {
                write!(f, "Error while constructing an IntervalConstraint: {err}")
            }
        }
    }
}

impl From<IntervalOrderError<Variable>> for IntervalConstraintConstructionError {
    fn from(value: IntervalOrderError<Variable>) -> Self {
        Self::VarError(value)
    }
}

impl From<IntervalOrderError<WeightedSum<Variable>>> for IntervalConstraintConstructionError {
    fn from(value: IntervalOrderError<WeightedSum<Variable>>) -> Self {
        Self::SumVarError(value)
    }
}

impl VariableConstraint for IntervalConstraint {
    fn as_boolean_expr(&self) -> BooleanExpression<Variable> {
        match self {
            IntervalConstraint::True => BooleanExpression::True,
            IntervalConstraint::False => BooleanExpression::False,
            IntervalConstraint::Conj(lhs, rhs) => BooleanExpression::BinaryExpression(
                Box::new(lhs.as_boolean_expr()),
                BooleanConnective::And,
                Box::new(rhs.as_boolean_expr()),
            ),
            IntervalConstraint::Disj(lhs, rhs) => BooleanExpression::BinaryExpression(
                Box::new(lhs.as_boolean_expr()),
                BooleanConnective::Or,
                Box::new(rhs.as_boolean_expr()),
            ),
            IntervalConstraint::SingleVarIntervalConstr(var, intervals) => {
                intervals.iter().fold(BooleanExpression::False, |acc, i| {
                    let b_expr = i.encode_into_boolean_expr(var);

                    BooleanExpression::BinaryExpression(
                        Box::new(acc),
                        BooleanConnective::Or,
                        Box::new(b_expr),
                    )
                })
            }
            IntervalConstraint::MultiVarIntervalConstr(vars, intervals) => {
                intervals.iter().fold(BooleanExpression::False, |acc, i| {
                    let b_expr = i.encode_into_boolean_expr(vars);

                    BooleanExpression::BinaryExpression(
                        Box::new(acc),
                        BooleanConnective::Or,
                        Box::new(b_expr),
                    )
                })
            }
        }
    }
}

/// Errors that can occur when trying to construct an interval automaton from a
/// general automaton
#[derive(Debug, PartialEq, Clone)]
pub enum IntervalTATransformationError {
    /// Error that occurred during while attempting to translate general ta into
    /// the linear arithmetic form
    LIATransformationError(Box<LIATransformationError>),
    /// Comparison Guard found in Rule during transformation
    ComparisonGuardFoundRule(Box<LIARule>),
    /// Comparison Guard found in Initial Variable Constraint during transformation
    ComparisonGuardFoundInitialVariableConstraint(Box<LIAVariableConstraint>),
    /// Comparison Guard found as part of the interval target
    ComparisonGuardFoundVariableTarget(Box<LIAVariableConstraint>),
}

impl fmt::Display for IntervalTATransformationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IntervalTATransformationError::LIATransformationError(e) => write!(
                f,
                "Failed to derive interval threshold automaton: Transformation to linear arithmetic automaton failed: Error: {e}"
            ),
            IntervalTATransformationError::ComparisonGuardFoundRule(rule) => write!(
                f,
                "Failed to derive interval threshold automaton: Found comparison guard which is unsupported. Rule: {rule}"
            ),
            IntervalTATransformationError::ComparisonGuardFoundInitialVariableConstraint(
                constr,
            ) => {
                write!(
                    f,
                    "Failed to derive interval threshold automaton: Found comparison guard in initial variable constraint which is unsupported. Initial variable constraint: {constr}"
                )
            }
            IntervalTATransformationError::ComparisonGuardFoundVariableTarget(constr) => {
                write!(
                    f,
                    "Failed to derive interval threshold automaton: Found comparison guard as part of a interval target constraint: {constr}"
                )
            }
        }
    }
}

impl error::Error for IntervalTATransformationError {}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, HashSet};

    use interval::IntervalBoundary;
    use taco_smt_encoder::SMTSolverBuilder;
    use taco_threshold_automaton::{
        expressions::{ComparisonOp, IntegerExpression, fraction::Fraction},
        general_threshold_automaton::{
            Action,
            builder::{GeneralThresholdAutomatonBuilder, RuleBuilder},
        },
        lia_threshold_automaton::{
            SingleAtomConstraint, SumAtomConstraint,
            integer_thresholds::{ThresholdCompOp, ThresholdConstraint},
        },
    };

    use super::*;

    #[test]
    fn test_interval_threshold_automaton_getters() {
        let var = Variable::new("x");
        let i1 = Interval::new_constant(0, 1);
        let i2 = Interval::new_constant(1, 2);
        let i3 = Interval::new(
            IntervalBoundary::from_const(2),
            false,
            IntervalBoundary::from_const(2),
            false,
        );
        let i4 = Interval::new(
            IntervalBoundary::from_const(2),
            true,
            IntervalBoundary::new_infty(),
            true,
        );

        let rc = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Param(Parameter::new("n"))),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Const(3)),
        );

        let ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_variable(var.clone())
            .unwrap()
            .with_locations([Location::new("l1"), Location::new("l2")])
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
                RuleBuilder::new(0, Location::new("l1"), Location::new("l2"))
                    .with_guard(BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(var.clone())),
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(2)),
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

        let rule = IntervalTARule::new(
            0,
            Location::new("l1"),
            Location::new("l2"),
            IntervalConstraint::SingleVarIntervalConstr(var.clone(), vec![i4.clone()]),
            vec![IntervalTAAction::new(
                var.clone(),
                IntervalActionEffect::Inc(1),
            )],
        );

        let mut interval_tas = IntervalTABuilder::new(lia_ta, SMTSolverBuilder::default(), vec![])
            .build()
            .unwrap();
        let interval_threshold_automaton = interval_tas.next().unwrap();
        assert!(interval_tas.next().is_none());

        assert_eq!(interval_threshold_automaton.name(), "test_ta");
        assert_eq!(
            interval_threshold_automaton
                .parameters()
                .map(|p| p.to_string())
                .collect::<HashSet<_>>(),
            HashSet::from(["n".to_string()])
        );
        assert_eq!(
            interval_threshold_automaton
                .resilience_conditions()
                .collect::<Vec<_>>(),
            vec![
                &rc,
                &BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Const(0)),
                    ComparisonOp::Lt,
                    Box::new(IntegerExpression::Const(1)),
                ),
                &BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Const(1)),
                    ComparisonOp::Lt,
                    Box::new(IntegerExpression::Const(2)),
                )
            ]
        );

        assert!(interval_threshold_automaton.is_declared(&Location::new("l1")));
        assert!(interval_threshold_automaton.is_declared(&Variable::new("x")));
        assert!(interval_threshold_automaton.is_declared(&Parameter::new("n")));

        assert_eq!(
            interval_threshold_automaton
                .incoming_rules(&Location::new("l2"))
                .collect::<Vec<_>>(),
            vec![&rule]
        );
        assert_eq!(
            interval_threshold_automaton
                .outgoing_rules(&Location::new("l1"))
                .collect::<Vec<_>>(),
            vec![&rule]
        );

        assert_eq!(
            interval_threshold_automaton.get_initial_interval(&var),
            vec![&i1, &i2, &i3, &i4,],
            "Got: {}\nExpected: {}",
            join_iterator(
                interval_threshold_automaton
                    .get_initial_interval(&var)
                    .iter(),
                ","
            ),
            join_iterator([&i1, &i2, &i3, &i4].iter(), ",")
        );
        assert_eq!(
            interval_threshold_automaton.get_zero_interval(&var),
            &Interval::zero()
        );
        assert_eq!(
            interval_threshold_automaton.get_intervals(&var),
            &vec![i1.clone(), i2.clone(), i3.clone(), i4.clone()]
        );
        assert_eq!(
            interval_threshold_automaton.get_previous_interval(&var, &i1),
            None
        );
        assert_eq!(
            interval_threshold_automaton.get_previous_interval(&var, &i2),
            Some(&i1)
        );
        assert_eq!(
            interval_threshold_automaton.get_previous_interval(&var, &i3),
            Some(&i2)
        );
        assert_eq!(
            interval_threshold_automaton.get_next_interval(&var, &i1),
            Some(&i2)
        );
        assert_eq!(
            interval_threshold_automaton.get_next_interval(&var, &i2),
            Some(&i3)
        );
        assert_eq!(
            interval_threshold_automaton.get_next_interval(&var, &i3),
            Some(&i4)
        );
        assert_eq!(
            interval_threshold_automaton.get_next_interval(&var, &i4),
            None
        );

        assert_eq!(
            interval_threshold_automaton
                .initial_location_constraints()
                .cloned()
                .collect::<Vec<_>>(),
            vec![BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Location::new("l1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            )]
        );
    }

    #[test]
    fn test_rule_getter() {
        let var = Variable::new("x");
        let i = Interval::new(
            IntervalBoundary::from_const(2),
            false,
            IntervalBoundary::new_infty(),
            true,
        );
        let rule = IntervalTARule::new(
            0,
            Location::new("l1"),
            Location::new("l2"),
            IntervalConstraint::SingleVarIntervalConstr(var.clone(), vec![i.clone()]),
            vec![],
        );

        assert_eq!(rule.id(), 0);
        assert_eq!(rule.source(), &Location::new("l1"));
        assert_eq!(rule.target(), &Location::new("l2"));
        assert_eq!(
            rule.guard(),
            &IntervalConstraint::SingleVarIntervalConstr(var.clone(), vec![i.clone()])
        );
    }

    #[test]
    fn test_display_abstract_rule() {
        let var = Variable::new("x");
        let i = Interval::new(
            IntervalBoundary::from_const(2),
            false,
            IntervalBoundary::new_infty(),
            true,
        );
        let rule = IntervalTARule::new(
            0,
            Location::new("l1"),
            Location::new("l2"),
            IntervalConstraint::SingleVarIntervalConstr(var.clone(), vec![i.clone()]),
            vec![IntervalTAAction::new(
                var.clone(),
                IntervalActionEffect::Reset,
            )],
        );

        assert_eq!(
            rule.to_string(),
            "0: l1 -> l2\n    when ( x ∈ { [2, ∞[ } )\n    do { x = 0 }"
        );

        let rule = IntervalTARule::new(
            1,
            Location::new("l1"),
            Location::new("l2"),
            IntervalConstraint::True,
            vec![IntervalTAAction::new(
                var.clone(),
                IntervalActionEffect::Inc(1),
            )],
        );

        assert_eq!(
            rule.to_string(),
            "1: l1 -> l2\n    when ( true )\n    do { x ++ }"
        );

        let var2 = Variable::new("y");
        let rule = IntervalTARule::new(
            3,
            Location::new("l1"),
            Location::new("l2"),
            IntervalConstraint::MultiVarIntervalConstr(
                WeightedSum::new(BTreeMap::from([(var.clone(), 1), (var2.clone(), 1)])),
                vec![i.clone()],
            ),
            vec![IntervalTAAction::new(
                var.clone(),
                IntervalActionEffect::Dec(2),
            )],
        );

        assert_eq!(
            rule.to_string(),
            "3: l1 -> l2\n    when ( x + y  ∈ { [2, ∞[ } )\n    do { x -- }"
        );
    }

    #[test]
    fn test_get_initial_intervals() {
        let var1 = Variable::new("x");
        let var2 = Variable::new("y");

        let i4 = Interval::new(
            IntervalBoundary::from_const(1),
            false,
            IntervalBoundary::Infty,
            true,
        );

        let rc = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Param(Parameter::new("n"))),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Const(3)),
        );

        let ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_variables([var1.clone(), var2.clone()])
            .unwrap()
            .with_locations([Location::new("l1"), Location::new("l2")])
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
            .with_initial_variable_constraints([BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(var1.clone())),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            )])
            .unwrap()
            .with_rule(
                RuleBuilder::new(0, Location::new("l1"), Location::new("l2"))
                    .with_guard(BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(var1.clone())),
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(2)),
                    ))
                    .with_action(
                        Action::new(
                            var1.clone(),
                            IntegerExpression::Const(1) + IntegerExpression::Atom(var1.clone()),
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

        assert_eq!(
            interval_threshold_automaton.get_initial_interval(&var1),
            vec![&Interval::zero(),]
        );
        assert_eq!(
            interval_threshold_automaton.get_initial_interval(&var2),
            vec![&Interval::zero(), &i4]
        );
    }

    #[test]
    fn test_interval_action_getters() {
        let var = Variable::new("x");
        let action = IntervalTAAction::new(var.clone(), IntervalActionEffect::Inc(1));

        assert_eq!(action.variable(), &var);
        assert!(!action.is_unchanged());
        assert!(!action.is_reset());
        assert!(action.is_increment());
        assert!(!action.is_decrement());

        let action = IntervalTAAction::new(var.clone(), IntervalActionEffect::Reset);

        assert_eq!(action.variable(), &var);
        assert!(!action.is_unchanged());
        assert!(action.is_reset());
        assert!(!action.is_increment());
        assert!(!action.is_decrement());

        let action = IntervalTAAction::new(var.clone(), IntervalActionEffect::Dec(1));

        assert_eq!(action.variable(), &var);
        assert!(!action.is_unchanged());
        assert!(!action.is_reset());
        assert!(!action.is_increment());
        assert!(action.is_decrement());
    }

    #[test]
    fn test_interval_guard_is_enabled() {
        let i1 = Interval::new_constant(0, 1);
        let i2 = Interval::new_constant(2, 3);
        let i3 = Interval::new_constant(4, 5);

        let var = Variable::new("x");
        let state = IntervalState {
            t_to_interval: HashMap::from([(var.clone(), i1.clone())]),
        };

        let guard = IntervalConstraint::SingleVarIntervalConstr(
            var.clone(),
            Vec::from([i1.clone(), i2.clone()]),
        );
        assert!(guard.is_enabled(&state).unwrap());

        let guard = IntervalConstraint::SingleVarIntervalConstr(
            var.clone(),
            Vec::from([i2.clone(), i3.clone()]),
        );
        assert!(!guard.is_enabled(&state).unwrap());

        let guard = IntervalConstraint::Conj(
            Box::new(IntervalConstraint::SingleVarIntervalConstr(
                var.clone(),
                Vec::from([i1.clone(), i3.clone()]),
            )),
            Box::new(IntervalConstraint::SingleVarIntervalConstr(
                var.clone(),
                Vec::from([i1.clone(), i2.clone()]),
            )),
        );
        assert!(guard.is_enabled(&state).unwrap());

        let guard = IntervalConstraint::Conj(
            Box::new(IntervalConstraint::SingleVarIntervalConstr(
                var.clone(),
                Vec::from([i1.clone(), i2.clone()]),
            )),
            Box::new(IntervalConstraint::SingleVarIntervalConstr(
                var.clone(),
                Vec::from([i3.clone()]),
            )),
        );
        assert!(!guard.is_enabled(&state).unwrap());

        let guard = IntervalConstraint::Disj(
            Box::new(IntervalConstraint::SingleVarIntervalConstr(
                var.clone(),
                Vec::from([i1.clone()]),
            )),
            Box::new(IntervalConstraint::SingleVarIntervalConstr(
                var.clone(),
                Vec::from([i3.clone()]),
            )),
        );
        assert!(guard.is_enabled(&state).unwrap());

        let guard = IntervalConstraint::Disj(
            Box::new(IntervalConstraint::SingleVarIntervalConstr(
                var.clone(),
                Vec::from([i2.clone()]),
            )),
            Box::new(IntervalConstraint::SingleVarIntervalConstr(
                var.clone(),
                Vec::from([i3.clone()]),
            )),
        );
        assert!(!guard.is_enabled(&state).unwrap());

        let guard = IntervalConstraint::True;
        assert!(guard.is_enabled(&state).unwrap());
    }

    #[test]
    fn test_interval_guard_is_enabled_error() {
        let i1 = Interval::new_constant(0, 1);

        let state: IntervalState<Variable> = IntervalState {
            t_to_interval: HashMap::new(),
        };

        let var = Variable::new("x");
        let guard =
            IntervalConstraint::SingleVarIntervalConstr(var.clone(), Vec::from([i1.clone()]));

        let err = guard.is_enabled(&state);
        assert!(matches!(err, Err(IntervalOrderError::VariableNotFound { var: v }) if v == var));
    }

    #[test]
    fn test_guard_to_boolean_expr() {
        let guard = IntervalConstraint::True;
        assert_eq!(guard.as_boolean_expr(), BooleanExpression::True);

        let guard = IntervalConstraint::False;
        assert_eq!(guard.as_boolean_expr(), BooleanExpression::False);

        let var = Variable::new("x");
        let i1 = Interval::new_constant(0, 1);
        let i2 = Interval::new_constant(1, 2);

        let guard =
            IntervalConstraint::SingleVarIntervalConstr(var.clone(), vec![i1.clone(), i2.clone()]);
        assert_eq!(
            guard.as_boolean_expr(),
            BooleanExpression::BinaryExpression(
                Box::new(BooleanExpression::BinaryExpression(
                    Box::new(BooleanExpression::False),
                    BooleanConnective::Or,
                    Box::new(BooleanExpression::BinaryExpression(
                        Box::new(BooleanExpression::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(var.clone())),
                            ComparisonOp::Geq,
                            Box::new(IntegerExpression::Const(0))
                        )),
                        BooleanConnective::And,
                        Box::new(BooleanExpression::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(var.clone())),
                            ComparisonOp::Lt,
                            Box::new(IntegerExpression::Const(1))
                        ))
                    )),
                )),
                BooleanConnective::Or,
                Box::new(BooleanExpression::BinaryExpression(
                    Box::new(BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(var.clone())),
                        ComparisonOp::Geq,
                        Box::new(IntegerExpression::Const(1))
                    )),
                    BooleanConnective::And,
                    Box::new(BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(var.clone())),
                        ComparisonOp::Lt,
                        Box::new(IntegerExpression::Const(2))
                    ))
                ))
            )
        );

        let guard = IntervalConstraint::MultiVarIntervalConstr(
            WeightedSum::new([(var.clone(), 1)]),
            vec![i1.clone(), i2.clone()],
        );
        assert_eq!(
            guard.as_boolean_expr(),
            BooleanExpression::BinaryExpression(
                Box::new(BooleanExpression::BinaryExpression(
                    Box::new(BooleanExpression::False),
                    BooleanConnective::Or,
                    Box::new(BooleanExpression::BinaryExpression(
                        Box::new(BooleanExpression::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(var.clone())),
                            ComparisonOp::Geq,
                            Box::new(IntegerExpression::Const(0))
                        )),
                        BooleanConnective::And,
                        Box::new(BooleanExpression::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(var.clone())),
                            ComparisonOp::Lt,
                            Box::new(IntegerExpression::Const(1))
                        ))
                    )),
                )),
                BooleanConnective::Or,
                Box::new(BooleanExpression::BinaryExpression(
                    Box::new(BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(var.clone())),
                        ComparisonOp::Geq,
                        Box::new(IntegerExpression::Const(1))
                    )),
                    BooleanConnective::And,
                    Box::new(BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(var.clone())),
                        ComparisonOp::Lt,
                        Box::new(IntegerExpression::Const(2))
                    ))
                ))
            )
        );

        let guard = IntervalConstraint::Conj(
            Box::new(IntervalConstraint::SingleVarIntervalConstr(
                var.clone(),
                vec![i1.clone()],
            )),
            Box::new(IntervalConstraint::SingleVarIntervalConstr(
                var.clone(),
                vec![i2.clone()],
            )),
        );
        assert_eq!(
            guard.as_boolean_expr(),
            BooleanExpression::BinaryExpression(
                Box::new(BooleanExpression::BinaryExpression(
                    Box::new(BooleanExpression::False),
                    BooleanConnective::Or,
                    Box::new(BooleanExpression::BinaryExpression(
                        Box::new(BooleanExpression::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(var.clone())),
                            ComparisonOp::Geq,
                            Box::new(IntegerExpression::Const(0))
                        )),
                        BooleanConnective::And,
                        Box::new(BooleanExpression::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(var.clone())),
                            ComparisonOp::Lt,
                            Box::new(IntegerExpression::Const(1))
                        ))
                    )),
                )),
                BooleanConnective::And,
                Box::new(BooleanExpression::BinaryExpression(
                    Box::new(BooleanExpression::False),
                    BooleanConnective::Or,
                    Box::new(BooleanExpression::BinaryExpression(
                        Box::new(BooleanExpression::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(var.clone())),
                            ComparisonOp::Geq,
                            Box::new(IntegerExpression::Const(1))
                        )),
                        BooleanConnective::And,
                        Box::new(BooleanExpression::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(var.clone())),
                            ComparisonOp::Lt,
                            Box::new(IntegerExpression::Const(2))
                        ))
                    )),
                )),
            )
        );

        let guard = IntervalConstraint::Disj(
            Box::new(IntervalConstraint::SingleVarIntervalConstr(
                var.clone(),
                vec![i1.clone()],
            )),
            Box::new(IntervalConstraint::SingleVarIntervalConstr(
                var.clone(),
                vec![i2.clone()],
            )),
        );

        assert_eq!(
            guard.as_boolean_expr(),
            BooleanExpression::BinaryExpression(
                Box::new(BooleanExpression::BinaryExpression(
                    Box::new(BooleanExpression::False),
                    BooleanConnective::Or,
                    Box::new(BooleanExpression::BinaryExpression(
                        Box::new(BooleanExpression::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(var.clone())),
                            ComparisonOp::Geq,
                            Box::new(IntegerExpression::Const(0))
                        )),
                        BooleanConnective::And,
                        Box::new(BooleanExpression::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(var.clone())),
                            ComparisonOp::Lt,
                            Box::new(IntegerExpression::Const(1))
                        ))
                    )),
                )),
                BooleanConnective::Or,
                Box::new(BooleanExpression::BinaryExpression(
                    Box::new(BooleanExpression::False),
                    BooleanConnective::Or,
                    Box::new(BooleanExpression::BinaryExpression(
                        Box::new(BooleanExpression::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(var.clone())),
                            ComparisonOp::Geq,
                            Box::new(IntegerExpression::Const(1))
                        )),
                        BooleanConnective::And,
                        Box::new(BooleanExpression::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(var.clone())),
                            ComparisonOp::Lt,
                            Box::new(IntegerExpression::Const(2))
                        ))
                    )),
                )),
            )
        );
    }

    #[test]
    fn test_display_interval_threshold_automaton() {
        let var = Variable::new("x");

        let rc = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Param(Parameter::new("n"))),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Const(3)),
        );

        let ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_variable(var.clone())
            .unwrap()
            .with_locations([Location::new("l1"), Location::new("l2")])
            .unwrap()
            .with_parameter(Parameter::new("n"))
            .unwrap()
            .initialize()
            .with_resilience_condition(rc.clone())
            .unwrap()
            .with_rule(
                RuleBuilder::new(0, Location::new("l1"), Location::new("l2"))
                    .with_guard(BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(var.clone())),
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(2)),
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

        let expected = "thresholdAutomaton test_ta {\n    intervalOrder {\n        x: [0, 1[, [1, 2[, [2, 2], ]2, ∞[;\n    }\n\n    shared x;\n\n    parameters n;\n\n    assumptions (3) {\n        n > 3;\n        0 < 1;\n        1 < 2;\n    }\n\n    locations (2) {\n        l1:[0];\n        l2:[1];\n    }\n\n    inits (0) {\n    }\n\n    rules (1) {\n        0: l1 -> l2\n            when ( x ∈ { ]2, ∞[ } )\n            do { x ++ };\n    }\n}\n";

        assert_eq!(interval_threshold_automaton.to_string(), expected);
    }

    #[test]
    fn test_interval_constraint_from_lia() {
        let i0 = Interval::new_constant(0, 1);
        let i1 = Interval::new_constant(1, 2);
        let i2 = Interval::new(
            IntervalBoundary::from_const(2),
            false,
            IntervalBoundary::new_bound(
                WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                Fraction::from(0),
            ),
            true,
        );
        let i3 = Interval::new(
            IntervalBoundary::new_bound(
                WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                Fraction::from(0),
            ),
            true,
            IntervalBoundary::Infty,
            true,
        );

        let order = StaticIntervalOrder::new(
            HashMap::from([(
                Variable::new("x"),
                vec![i0.clone(), i1.clone(), i2.clone(), i3.clone()],
            )]),
            HashMap::from([(
                WeightedSum::new([
                    (Variable::new("x"), Fraction::from(1)),
                    (Variable::new("y"), Fraction::from(1)),
                ]),
                vec![i0.clone(), i1.clone(), i2.clone(), i3.clone()],
            )]),
            HashMap::new(),
        );

        // x > 2
        let lguard = LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint::new(
            Variable::new("x"),
            ThresholdConstraint::new(
                ThresholdCompOp::Geq,
                Vec::<(_, u32)>::new(),
                Fraction::from(2),
            ),
        ));
        let got_guard = IntervalConstraint::from_lia_constr(&lguard, &order).unwrap();
        let expected_guard = IntervalConstraint::SingleVarIntervalConstr(
            Variable::new("x"),
            vec![i2.clone(), i3.clone()],
        );
        // x ∈ {[2, ∞[}
        assert_eq!(
            got_guard, expected_guard,
            "Got {got_guard} \n Expected {expected_guard}"
        );

        // x + y < 2
        let lguard = LIAVariableConstraint::SumVarConstraint(
            SumAtomConstraint::try_new(
                [
                    (Variable::new("x"), Fraction::from(1)),
                    (Variable::new("y"), Fraction::from(1)),
                ],
                ThresholdConstraint::new(
                    ThresholdCompOp::Lt,
                    Vec::<(_, u32)>::new(),
                    Fraction::from(2),
                ),
            )
            .unwrap(),
        );
        let got_guard = IntervalConstraint::from_lia_constr(&lguard, &order).unwrap();
        let expected_guard = IntervalConstraint::MultiVarIntervalConstr(
            WeightedSum::new([
                (Variable::new("x"), Fraction::from(1)),
                (Variable::new("y"), Fraction::from(1)),
            ]),
            vec![i0.clone(), i1.clone()],
        );
        // x + y ∈ {[0, 1[, [1, 2[}
        assert_eq!(
            got_guard, expected_guard,
            "Got {got_guard} \n Expected {expected_guard}"
        );

        // x < 2 && x >= 1
        let lguard = LIAVariableConstraint::BinaryGuard(
            Box::new(LIAVariableConstraint::SingleVarConstraint(
                SingleAtomConstraint::new(
                    Variable::new("x"),
                    ThresholdConstraint::new(
                        ThresholdCompOp::Lt,
                        Vec::<(_, u32)>::new(),
                        Fraction::from(2),
                    ),
                ),
            )),
            BooleanConnective::And,
            Box::new(LIAVariableConstraint::SingleVarConstraint(
                SingleAtomConstraint::new(
                    Variable::new("x"),
                    ThresholdConstraint::new(
                        ThresholdCompOp::Geq,
                        Vec::<(_, u32)>::new(),
                        Fraction::from(1),
                    ),
                ),
            )),
        );
        let got_guard = IntervalConstraint::from_lia_constr(&lguard, &order).unwrap();
        let expected_guard = IntervalConstraint::Conj(
            Box::new(IntervalConstraint::SingleVarIntervalConstr(
                Variable::new("x"),
                vec![i0.clone(), i1.clone()],
            )),
            Box::new(IntervalConstraint::SingleVarIntervalConstr(
                Variable::new("x"),
                vec![i1.clone(), i2.clone(), i3.clone()],
            )),
        );
        // x ∈ {[0,1[, [1, 2[} && {[1,2[, [2, ∞[}
        assert_eq!(
            got_guard, expected_guard,
            "Got {got_guard} \n Expected {expected_guard}"
        );

        // x < 2 || x >= 1
        let lguard = LIAVariableConstraint::BinaryGuard(
            Box::new(LIAVariableConstraint::SingleVarConstraint(
                SingleAtomConstraint::new(
                    Variable::new("x"),
                    ThresholdConstraint::new(
                        ThresholdCompOp::Lt,
                        Vec::<(_, u32)>::new(),
                        Fraction::from(2),
                    ),
                ),
            )),
            BooleanConnective::Or,
            Box::new(LIAVariableConstraint::SingleVarConstraint(
                SingleAtomConstraint::new(
                    Variable::new("x"),
                    ThresholdConstraint::new(
                        ThresholdCompOp::Geq,
                        Vec::<(_, u32)>::new(),
                        Fraction::from(1),
                    ),
                ),
            )),
        );
        let got_guard = IntervalConstraint::from_lia_constr(&lguard, &order).unwrap();
        let expected_guard = IntervalConstraint::Disj(
            Box::new(IntervalConstraint::SingleVarIntervalConstr(
                Variable::new("x"),
                vec![i0.clone(), i1.clone()],
            )),
            Box::new(IntervalConstraint::SingleVarIntervalConstr(
                Variable::new("x"),
                vec![i1.clone(), i2.clone(), i3.clone()],
            )),
        );
        // x ∈ {[0,1[, [1, 2[} || {[1,2[, [2, ∞[}
        assert_eq!(
            got_guard, expected_guard,
            "Got {got_guard} \n Expected {expected_guard}"
        );
    }

    #[test]
    fn test_from_lia_simplify_and() {
        let i0 = Interval::new_constant(0, 1);
        let i1 = Interval::new_constant(1, 2);
        let i2 = Interval::new(
            IntervalBoundary::from_const(2),
            false,
            IntervalBoundary::new_bound(
                WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                Fraction::from(0),
            ),
            true,
        );
        let i3 = Interval::new(
            IntervalBoundary::new_bound(
                WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                Fraction::from(0),
            ),
            true,
            IntervalBoundary::Infty,
            true,
        );

        let order = StaticIntervalOrder::new(
            HashMap::from([(
                Variable::new("x"),
                vec![i0.clone(), i1.clone(), i2.clone(), i3.clone()],
            )]),
            HashMap::from([(
                WeightedSum::new([
                    (Variable::new("x"), Fraction::from(1)),
                    (Variable::new("y"), Fraction::from(1)),
                ]),
                vec![i0.clone(), i1.clone(), i2.clone(), i3.clone()],
            )]),
            HashMap::new(),
        );

        // (x >= 2) && true
        let lguard = LIAVariableConstraint::BinaryGuard(
            Box::new(LIAVariableConstraint::SingleVarConstraint(
                SingleAtomConstraint::new(
                    Variable::new("x"),
                    ThresholdConstraint::new(
                        ThresholdCompOp::Geq,
                        Vec::<(_, u32)>::new(),
                        Fraction::from(2),
                    ),
                ),
            )),
            BooleanConnective::And,
            Box::new(LIAVariableConstraint::True),
        );
        let got_guard = IntervalConstraint::from_lia_constr(&lguard, &order).unwrap();
        let expected_guard = IntervalConstraint::SingleVarIntervalConstr(
            Variable::new("x"),
            vec![i2.clone(), i3.clone()],
        );
        // x ∈ {[2, ∞[}
        assert_eq!(
            got_guard, expected_guard,
            "Got {got_guard} \n Expected {expected_guard}"
        );

        // true && (x >= 2)
        let lguard = LIAVariableConstraint::BinaryGuard(
            Box::new(LIAVariableConstraint::True),
            BooleanConnective::And,
            Box::new(LIAVariableConstraint::SingleVarConstraint(
                SingleAtomConstraint::new(
                    Variable::new("x"),
                    ThresholdConstraint::new(
                        ThresholdCompOp::Geq,
                        Vec::<(_, u32)>::new(),
                        Fraction::from(2),
                    ),
                ),
            )),
        );
        let got_guard = IntervalConstraint::from_lia_constr(&lguard, &order).unwrap();
        let expected_guard = IntervalConstraint::SingleVarIntervalConstr(
            Variable::new("x"),
            vec![i2.clone(), i3.clone()],
        );
        // x ∈ {[2, ∞[}
        assert_eq!(
            got_guard, expected_guard,
            "Got {got_guard} \n Expected {expected_guard}"
        );
    }

    #[test]
    fn test_from_lia_simplify_or() {
        let i0 = Interval::new_constant(0, 1);
        let i1 = Interval::new_constant(1, 2);
        let i2 = Interval::new(
            IntervalBoundary::from_const(2),
            false,
            IntervalBoundary::new_bound(
                WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                Fraction::from(0),
            ),
            true,
        );
        let i3 = Interval::new(
            IntervalBoundary::new_bound(
                WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                Fraction::from(0),
            ),
            true,
            IntervalBoundary::Infty,
            true,
        );

        let order = StaticIntervalOrder::new(
            HashMap::from([(
                Variable::new("x"),
                vec![i0.clone(), i1.clone(), i2.clone(), i3.clone()],
            )]),
            HashMap::from([(
                WeightedSum::new([
                    (Variable::new("x"), Fraction::from(1)),
                    (Variable::new("y"), Fraction::from(1)),
                ]),
                vec![i0.clone(), i1.clone(), i2.clone(), i3.clone()],
            )]),
            HashMap::new(),
        );

        // (x >= 2) || false
        let lguard = LIAVariableConstraint::BinaryGuard(
            Box::new(LIAVariableConstraint::SingleVarConstraint(
                SingleAtomConstraint::new(
                    Variable::new("x"),
                    ThresholdConstraint::new(
                        ThresholdCompOp::Geq,
                        Vec::<(_, u32)>::new(),
                        Fraction::from(2),
                    ),
                ),
            )),
            BooleanConnective::Or,
            Box::new(LIAVariableConstraint::False),
        );
        let got_guard = IntervalConstraint::from_lia_constr(&lguard, &order).unwrap();
        let expected_guard = IntervalConstraint::SingleVarIntervalConstr(
            Variable::new("x"),
            vec![i2.clone(), i3.clone()],
        );
        // x ∈ {[2, ∞[}
        assert_eq!(
            got_guard, expected_guard,
            "Got {got_guard} \n Expected {expected_guard}"
        );

        // false || (x >= 2)
        let lguard = LIAVariableConstraint::BinaryGuard(
            Box::new(LIAVariableConstraint::False),
            BooleanConnective::Or,
            Box::new(LIAVariableConstraint::SingleVarConstraint(
                SingleAtomConstraint::new(
                    Variable::new("x"),
                    ThresholdConstraint::new(
                        ThresholdCompOp::Geq,
                        Vec::<(_, u32)>::new(),
                        Fraction::from(2),
                    ),
                ),
            )),
        );
        let got_guard = IntervalConstraint::from_lia_constr(&lguard, &order).unwrap();
        let expected_guard = IntervalConstraint::SingleVarIntervalConstr(
            Variable::new("x"),
            vec![i2.clone(), i3.clone()],
        );
        // x ∈ {[2, ∞[}
        assert_eq!(
            got_guard, expected_guard,
            "Got {got_guard} \n Expected {expected_guard}"
        );
    }

    #[test]
    fn test_from_lia_simplify_interval_all_or_none() {
        let i0 = Interval::new_constant(0, 1);
        let i1 = Interval::new_constant(1, 2);
        let i2 = Interval::new(
            IntervalBoundary::from_const(2),
            false,
            IntervalBoundary::new_bound(
                WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                Fraction::from(0),
            ),
            true,
        );
        let i3 = Interval::new(
            IntervalBoundary::new_bound(
                WeightedSum::new([(Parameter::new("n"), Fraction::from(1))]),
                Fraction::from(0),
            ),
            true,
            IntervalBoundary::Infty,
            true,
        );

        let order = StaticIntervalOrder::new(
            HashMap::from([(
                Variable::new("x"),
                vec![i0.clone(), i1.clone(), i2.clone(), i3.clone()],
            )]),
            HashMap::from([(
                WeightedSum::new([
                    (Variable::new("x"), Fraction::from(1)),
                    (Variable::new("y"), Fraction::from(1)),
                ]),
                vec![i0.clone(), i1.clone(), i2.clone(), i3.clone()],
            )]),
            HashMap::new(),
        );

        // x >= 0
        let lguard = LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint::new(
            Variable::new("x"),
            ThresholdConstraint::new(
                ThresholdCompOp::Geq,
                Vec::<(_, u32)>::new(),
                Fraction::from(0),
            ),
        ));
        let got_guard = IntervalConstraint::from_lia_constr(&lguard, &order).unwrap();
        let expected_guard = IntervalConstraint::True;
        // true
        assert_eq!(
            got_guard, expected_guard,
            "Got {got_guard} \n Expected {expected_guard}"
        );

        // x < 0
        let lguard = LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint::new(
            Variable::new("x"),
            ThresholdConstraint::new(
                ThresholdCompOp::Lt,
                Vec::<(_, u32)>::new(),
                Fraction::from(0),
            ),
        ));
        let got_guard = IntervalConstraint::from_lia_constr(&lguard, &order).unwrap();
        let expected_guard = IntervalConstraint::False;
        // true
        assert_eq!(
            got_guard, expected_guard,
            "Got {got_guard} \n Expected {expected_guard}"
        );
    }

    #[test]
    fn test_get_interval_constr() {
        let var = Variable::new("x");

        let rc = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Param(Parameter::new("n"))),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Const(3)),
        );

        let ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_variables([var.clone(), Variable::new("y")])
            .unwrap()
            .with_locations([Location::new("l1"), Location::new("l2")])
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
                RuleBuilder::new(0, Location::new("l1"), Location::new("l2"))
                    .with_guard(BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(var.clone())),
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(2)),
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

        let lia_constr: LIAVariableConstraint = (&BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Variable::new("x"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        ))
            .try_into()
            .unwrap();

        let mut interval_tas = IntervalTABuilder::new(
            lia_ta,
            SMTSolverBuilder::default(),
            vec![lia_constr.clone()],
        )
        .build()
        .unwrap();
        let interval_ta = interval_tas.next().unwrap();

        let expected_interval_constr = IntervalConstraint::SingleVarIntervalConstr(
            Variable::new("x"),
            vec![Interval::new_constant(0, 1)],
        );

        assert_eq!(
            interval_ta.get_interval_constraint(&lia_constr).unwrap(),
            expected_interval_constr
        )
    }

    #[test]
    fn test_get_interval_constr_unknown_var() {
        let var = Variable::new("x");

        let rc = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Param(Parameter::new("n"))),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Const(3)),
        );

        let ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_variables([var.clone(), Variable::new("y")])
            .unwrap()
            .with_locations([Location::new("l1"), Location::new("l2")])
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
                RuleBuilder::new(0, Location::new("l1"), Location::new("l2"))
                    .with_guard(BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(var.clone())),
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(2)),
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
        let interval_ta = interval_tas.next().unwrap();

        let lia_constr: LIAVariableConstraint = (&BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Variable::new("unknown"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        ))
            .try_into()
            .unwrap();

        let got_interval_constr = interval_ta.get_interval_constraint(&lia_constr);

        assert!(got_interval_constr.is_err());
        assert_eq!(
            got_interval_constr.unwrap_err(),
            IntervalConstraintConstructionError::VarError(IntervalOrderError::VariableNotFound {
                var: Variable::new("unknown")
            })
        )
    }

    #[test]
    fn test_get_constrained_variables() {
        let var = Variable::new("x");

        let rc = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Param(Parameter::new("n"))),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Const(3)),
        );

        let ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_variables([var.clone(), Variable::new("y")])
            .unwrap()
            .with_locations([Location::new("l1"), Location::new("l2")])
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
                RuleBuilder::new(0, Location::new("l1"), Location::new("l2"))
                    .with_guard(BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(var.clone())),
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(2)),
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

        let lia_constr: LIAVariableConstraint = (&BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Variable::new("x"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(10)),
        ))
            .try_into()
            .unwrap();

        let mut interval_tas = IntervalTABuilder::new(
            lia_ta,
            SMTSolverBuilder::default(),
            vec![lia_constr.clone()],
        )
        .build()
        .unwrap();
        let interval_ta = interval_tas.next().unwrap();

        let interval_constr = interval_ta.get_interval_constraint(&lia_constr).unwrap();

        assert_eq!(
            interval_ta.get_variables_constrained(&interval_constr),
            vec![&Variable::new("x")]
        )
    }

    #[test]
    fn test_display_interval_constraint_construction_error() {
        let var_error: IntervalConstraintConstructionError = IntervalOrderError::VariableNotFound {
            var: Variable::new("x"),
        }
        .into();
        assert!(
            var_error
                .to_string()
                .contains("Error while constructing an IntervalConstraint:"),
        );

        let sum_var_error: IntervalConstraintConstructionError =
            IntervalOrderError::VariableNotFound {
                var: WeightedSum::new([(Variable::new("x"), 1), (Variable::new("y"), 1)]),
            }
            .into();
        assert!(
            sum_var_error
                .to_string()
                .contains("Error while constructing an IntervalConstraint:"),
        );
    }

    #[test]
    fn test_display_interval_ta_transformation_error() {
        let var = Variable::new("x");
        let rule = RuleBuilder::new(0, Location::new("l1"), Location::new("l2"))
            .with_guard(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(var.clone())),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Atom(Variable::new("y"))),
            ))
            .build()
            .try_into()
            .unwrap();
        let error = IntervalTATransformationError::ComparisonGuardFoundRule(Box::new(rule));
        assert!(
            error
                .to_string()
                .contains("Found comparison guard which is unsupported")
        );

        let constr: LIAVariableConstraint = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(var.clone())),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Atom(Variable::new("y"))),
        )
        .try_into()
        .unwrap();
        let error = IntervalTATransformationError::ComparisonGuardFoundInitialVariableConstraint(
            Box::new(constr.clone()),
        );
        assert!(
            error
                .to_string()
                .contains("Found comparison guard in initial variable constraint")
        );

        let error =
            IntervalTATransformationError::ComparisonGuardFoundVariableTarget(Box::new(constr));
        assert!(
            error
                .to_string()
                .contains("Found comparison guard as part of a interval target constraint")
        );
    }

    #[test]
    fn test_and_trait_and_bitand_operator() {
        let var = Variable::new("x");
        let i1 = Interval::new_constant(0, 1);
        let i2 = Interval::new_constant(1, 2);

        let lhs = IntervalConstraint::SingleVarIntervalConstr(var.clone(), vec![i1.clone()]);
        let rhs = IntervalConstraint::SingleVarIntervalConstr(var.clone(), vec![i2.clone()]);

        let lhs_clone = lhs.clone();
        let expected = IntervalConstraint::Conj(Box::new(lhs_clone.clone()), Box::new(rhs.clone()));

        // The `and` method of the `And` trait combines both constraints with a
        // conjunction, keeping the operand order
        assert_eq!(lhs_clone.and(rhs.clone()), expected);

        // The `&` operator delegates to `And::and`
        assert_eq!(lhs & rhs, expected);
    }

    #[test]
    fn test_or_trait_and_bitor_operator() {
        let var = Variable::new("x");
        let i1 = Interval::new_constant(0, 1);
        let i2 = Interval::new_constant(1, 2);

        let lhs = IntervalConstraint::SingleVarIntervalConstr(var.clone(), vec![i1.clone()]);
        let rhs = IntervalConstraint::SingleVarIntervalConstr(var.clone(), vec![i2.clone()]);

        let lhs_clone = lhs.clone();
        let expected = IntervalConstraint::Disj(Box::new(lhs_clone.clone()), Box::new(rhs.clone()));

        // The `or` method of the `Or` trait combines both constraints with a
        // disjunction, keeping the operand order
        assert_eq!(lhs_clone.or(rhs.clone()), expected);

        // The `|` operator delegates to `Or::or`
        assert_eq!(lhs | rhs, expected);
    }
}
