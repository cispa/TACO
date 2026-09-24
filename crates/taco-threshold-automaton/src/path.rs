//! Concrete Paths in a Threshold Automaton
//!
//! This module defines the types for concrete paths in a threshold automaton.
//! Such a path can, for example, be used to represent a counterexample to a
//! specification.
//!
//! A full path is represented by a [`Path`] object that contains a sequence of
//! [`Configuration`]s and [`Transition`]s.
//!
//! To construct a [`Path`], a [`PathBuilder`] should be used, as it will ensure
//! that the constructed path is valid in the threshold automaton.

use std::{
    collections::HashMap,
    error,
    fmt::{self},
    hash,
};

use taco_display_utils::join_iterator;

use crate::{
    ActionDefinition, RuleDefinition, ThresholdAutomaton,
    expressions::{
        Atomic, BooleanExpression, Location, Parameter, Variable, properties::EvaluationError,
    },
    general_threshold_automaton::{GeneralThresholdAutomaton, Rule, UpdateExpression},
};

/// Global configuration of in a threshold automaton
///
/// A configuration specifies how many processes are in each location of the
/// threshold automaton and the valuation of the shared variables
#[derive(Debug, Clone, PartialEq)]
pub struct Configuration {
    /// Valuation of the shared variables
    variable_assignment: HashMap<Variable, u32>,
    /// Number of processes per location
    location_assignment: HashMap<Location, u32>,
}
impl Configuration {
    /// Create a new configuration
    ///
    /// This function creates a new configuration with the given variable and
    /// location assignments.
    ///
    /// The variable and location assignments are represented as [`HashMap`]s,
    /// where the keys are the variables and locations, and the values are the
    /// number of processes in the respective location or the value of the
    /// variable.
    pub fn new<T, S>(variable_assignment: T, location_assignment: S) -> Self
    where
        T: Into<HashMap<Variable, u32>>,
        S: Into<HashMap<Location, u32>>,
    {
        Configuration {
            variable_assignment: variable_assignment.into(),
            location_assignment: location_assignment.into(),
        }
    }

    /// Number of processes in location `loc`
    ///
    /// This function returns the number of processes in the given location
    /// `loc`. If the location is not known in the configuration, the function
    /// returns `0`.
    pub fn get_processes_in_location(&self, loc: &Location) -> u32 {
        *self.location_assignment.get(loc).unwrap_or(&0)
    }

    /// Current value of variable
    ///
    /// This function returns the value of the variable `var` in the configuration.
    /// If the variable is not known in the configuration, the function returns `0`.
    pub fn get_variable_value(&self, var: &Variable) -> u32 {
        *self.variable_assignment.get(var).unwrap_or(&0)
    }

    /// Iterator over the variable assignment
    ///
    /// This function returns an iterator over the variable assignment,
    /// where each item is a tuple of the variable and its value.
    pub fn variable_assignment(&self) -> impl Iterator<Item = (&Variable, &u32)> {
        self.variable_assignment.iter()
    }

    /// Iterator over the location assignment
    ///
    /// This function returns an iterator over the location assignment,
    /// where each item is a tuple of the location and the number of processes
    /// in it.
    pub fn location_assignment(&self) -> impl Iterator<Item = (&Location, &u32)> {
        self.location_assignment.iter()
    }

    /// Create the successor configuration after applying a transition
    ///
    /// Returns `None` if the transition cannot be applied to the configuration.
    /// This can for example happen if the source location of the applied rule
    /// has no processes or not enough processes to apply the rule.
    pub fn apply_rule(&self, tr: &Transition) -> Option<Self> {
        // Check whether the source location has at least one process (necessary
        // for self-loops)
        if *self.location_assignment.get(tr.rule_used.source())? == 0 {
            return None;
        }

        let mut new_loc_assignment = self.location_assignment.clone();
        let mut new_var_assignment = self.variable_assignment.clone();

        new_loc_assignment
            .entry(tr.rule_used.target().clone())
            .and_modify(|e| *e += tr.number_applied);

        if let Some(e) = new_loc_assignment.get_mut(tr.rule_used.source()) {
            {
                let sub = e.checked_sub(tr.number_applied)?;
                *e = sub;
            }
        }

        for act in tr.rule_used.actions() {
            let var = act.variable();

            match act.update() {
                UpdateExpression::Inc(i) => {
                    *new_var_assignment.entry(var.clone()).or_insert(0) += tr.number_applied * i;
                }
                UpdateExpression::Dec(d) => {
                    *new_var_assignment.entry(var.clone()).or_insert(0) -= tr.number_applied * d;
                }
                UpdateExpression::Reset => _ = new_var_assignment.insert(var.clone(), 0),
                UpdateExpression::Unchanged => continue,
            }
        }

        Some(Self {
            variable_assignment: new_var_assignment,
            location_assignment: new_loc_assignment,
        })
    }

    /// Returns a compact representation of the configuration skipping locations
    /// and variables which are assigned 0
    pub fn display_compact(&self) -> String {
        let mut locs = self
            .location_assignment
            .iter()
            .filter(|(_, n)| **n > 0)
            .map(|(l, _)| l)
            .collect::<Vec<_>>();
        locs.sort_by_key(|loc| loc.name());
        let locs = join_iterator(
            locs.into_iter()
                .map(|loc| format!("{} : {}", loc.name(), self.location_assignment[loc])),
            ", ",
        );

        let mut vars = self
            .variable_assignment
            .iter()
            .filter(|(_, n)| **n > 0)
            .map(|(v, _)| v)
            .collect::<Vec<_>>();
        vars.sort_by_key(|var| var.name());
        let vars = join_iterator(
            vars.into_iter()
                .map(|var| format!("{} : {}", var.name(), self.variable_assignment[var])),
            ", ",
        );

        format!("locations: ({locs}), variables: ({vars})")
    }
}

/// Transition that applying a rule a certain number of times
///
/// This struct represents a transition in a threshold automaton that applies a
/// rule a fixed number of times. It contains the rule that is applied and the
/// number of times the rule is applied.
/// In the literature such transitions are often called accelerated.
#[derive(Debug, Clone, PartialEq)]
pub struct Transition {
    /// Rule that is applied in this transition
    rule_used: Rule,
    /// Number of times the rule is applied
    number_applied: u32,
}

impl Transition {
    /// Creates a new transition
    ///
    /// Creates a new transition that applies the given [`Rule`] `n` times.
    pub fn new(rule_used: Rule, n: u32) -> Self {
        Transition {
            rule_used,
            number_applied: n,
        }
    }

    /// Get the rule of the transition
    pub fn rule(&self) -> &Rule {
        &self.rule_used
    }

    /// Check whether the transition does not change the current configuration
    ///
    /// Returns true if this transition does neither update the overall location
    /// state nor the variable state
    pub fn is_noop(&self) -> bool {
        self.number_applied == 0
            || (self.rule_used.source() == self.rule_used.target()
                && self.rule_used.actions().all(|act| act.is_unchanged()))
    }
}

/// Concrete path in a [`GeneralThresholdAutomaton`]
///
/// This struct represents a concrete path in a [`GeneralThresholdAutomaton`],
/// which consists of a sequence of configurations and transitions between them.
#[derive(Debug, Clone, PartialEq)]
pub struct Path {
    /// The threshold automaton this path belongs to
    ta: GeneralThresholdAutomaton,
    /// Parameter assignment for the path
    parameter_assignment: HashMap<Parameter, u32>,
    /// Configurations of the path
    configurations: Vec<Configuration>,
    /// Transitions of the path
    transitions: Vec<Transition>,
}
impl Path {
    /// Get the value of parameter `param` in the path
    pub fn get_parameter_value(&self, param: &Parameter) -> Option<u32> {
        self.parameter_assignment.get(param).cloned()
    }

    /// Returns an iterator over the parameters and their values in the path
    pub fn parameter_values(&self) -> impl Iterator<Item = (&Parameter, &u32)> {
        self.parameter_assignment.iter()
    }

    /// Iterator over the configurations of the path
    pub fn configurations(&self) -> impl Iterator<Item = &Configuration> {
        self.configurations.iter()
    }

    /// Iterator over the transitions of the path
    pub fn transitions(&self) -> impl Iterator<Item = &Transition> {
        self.transitions.iter()
    }

    /// Get a string representation of the path
    pub fn display_compact(&self) -> String {
        debug_assert!(self.configurations.len() == self.transitions.len() + 1);

        let mut res = format!("Path of threshold automaton {}: \n", self.ta.name());

        let param = display_assignment(self.parameter_assignment.clone());
        res += &format!("parameters: {param}\n");

        let mut it_transitions = self.transitions.iter();
        for (n_config, config) in self.configurations.iter().enumerate() {
            res += &format!("Configuration {n_config}: {}\n", config.display_compact());
            if let Some(transition) = it_transitions.next() {
                res += "        |\n";
                res += &format!("        |{transition}\n");
                res += "        V\n";
            }
        }

        res
    }
}

/// Builder for creating a path of a [`GeneralThresholdAutomaton`]
///
/// This builder allows to create a path of a [`GeneralThresholdAutomaton`] by
/// adding configurations and transitions between them. It then verifies that
/// the configurations and transitions are a valid path in the threshold
/// automaton.
///
/// First, this builder needs to be initialized with a
/// [`GeneralThresholdAutomaton`] and an assignment of parameters. Then it can
/// be transformed into an [`InitializedPathBuilder`] using
/// [`PathBuilder::add_parameter_assignment`], which then configurations and
/// transitions can be added.
#[derive(Debug, Clone, PartialEq)]
pub struct PathBuilder {
    ta: GeneralThresholdAutomaton,
    parameter_assignment: HashMap<Parameter, u32>,
}

impl PathBuilder {
    /// Create a new path builder for the given [`GeneralThresholdAutomaton`]
    pub fn new(ta: GeneralThresholdAutomaton) -> Self {
        Self {
            ta,
            parameter_assignment: HashMap::new(),
        }
    }

    /// Add a parameter assignment to the path and validate it against the
    /// resilience conditions of the threshold automaton
    pub fn add_parameter_assignment(
        mut self,
        param_evaluation: impl Into<HashMap<Parameter, u32>>,
    ) -> Result<InitializedPathBuilder, PathBuilderError> {
        let param_evaluation = param_evaluation.into();

        self.ta.resilience_conditions().try_for_each(|cond| {
            if !cond
                .check_satisfied(&HashMap::new(), &param_evaluation)
                .map_err(PathBuilderError::from)?
            {
                return Err(PathBuilderError::ResilienceConditionNotSatisfied(
                    Box::new(cond.clone()),
                    Box::new(param_evaluation.clone()),
                ));
            }

            Ok(())
        })?;

        self.parameter_assignment = param_evaluation;

        Ok(InitializedPathBuilder {
            ta: self.ta,
            n_processes: 0,
            parameter_assignment: self.parameter_assignment,
            configurations: Vec::new(),
            transitions: Vec::new(),
        })
    }
}

/// Builder for creating a validated [`Path`] of a [`GeneralThresholdAutomaton`]
/// that has been initialized with a threshold automaton and a parameter
/// assignment.
///
/// This type should always be derived from a [`PathBuilder`].
#[derive(Debug, Clone, PartialEq)]
pub struct InitializedPathBuilder {
    /// Threshold automaton this path belongs to
    ta: GeneralThresholdAutomaton,
    /// Number of processes in the path, will be initialized with the first configuration
    n_processes: u32,
    /// Parameter assignment for the path
    parameter_assignment: HashMap<Parameter, u32>,
    /// Configurations of the path
    configurations: Vec<Configuration>,
    /// Transitions of the path
    transitions: Vec<Transition>,
}

impl InitializedPathBuilder {
    /// Add a configuration to the path
    pub fn add_configuration(mut self, config: Configuration) -> Result<Self, PathBuilderError> {
        self.validate_configuration(&config)?;
        self.configurations.push(config);
        Ok(self)
    }

    /// Add multiple configurations to the path
    pub fn add_configurations(
        self,
        configs: impl IntoIterator<Item = Configuration>,
    ) -> Result<Self, PathBuilderError> {
        let mut builder = self;

        for config in configs {
            builder = builder.add_configuration(config)?;
        }

        Ok(builder)
    }

    /// Add a transition to the path
    pub fn add_transition(mut self, transition: Transition) -> Result<Self, PathBuilderError> {
        // Check that the rule used in the transition are valid
        if !self.ta.rules().any(|r| *r == transition.rule_used) {
            return Err(PathBuilderError::UnknownRule(transition.rule_used.clone()));
        }

        self.transitions.push(transition);

        Ok(self)
    }

    /// Add multiple transitions to the path
    pub fn add_transitions(
        mut self,
        transitions: impl IntoIterator<Item = Transition>,
    ) -> Result<Self, PathBuilderError> {
        for transition in transitions {
            self = self.add_transition(transition)?;
        }

        Ok(self)
    }

    /// Returns the last configuration that was added to the path builder
    pub fn last_configuration(&self) -> Option<&Configuration> {
        self.configurations.last()
    }

    /// Initial validation function of an inserted configuration
    fn validate_configuration(&mut self, config: &Configuration) -> Result<(), PathBuilderError> {
        // Check that all locations are present in the location assignment
        for loc in self.ta.locations() {
            if !config.location_assignment.contains_key(loc) {
                return Err(PathBuilderError::MissingLocation(loc.clone()));
            }
        }

        // Check that all variables are present in the variable assignment
        for var in self.ta.variables() {
            if !config.variable_assignment.contains_key(var) {
                return Err(PathBuilderError::MissingVariable(var.clone()));
            }
        }

        // If this is the first configuration, validate the initial configuration
        if self.configurations.is_empty() {
            Self::validate_initial_configuration(self, config)?;
            self.n_processes = config.location_assignment.values().sum();
            return Ok(());
        }

        // Check that the number of processes is consistent between configurations
        if self.n_processes != config.location_assignment.values().sum() {
            return Err(PathBuilderError::InconsistentNumberOfProcesses {
                initial_n: self.n_processes,
                config_n: config.location_assignment.values().sum(),
            });
        }

        Ok(())
    }

    /// Validate the initial configuration of the path
    fn validate_initial_configuration(
        &self,
        config: &Configuration,
    ) -> Result<(), PathBuilderError> {
        // Check that the initial location constraint is satisfied
        for loc_constr in self.ta.initial_location_conditions() {
            if !loc_constr
                .check_satisfied(&config.location_assignment, &self.parameter_assignment)
                .map_err(PathBuilderError::from)?
            {
                return Err(PathBuilderError::InitialLocationConstraintNotSatisfied(
                    Box::new(loc_constr.clone()),
                    Box::new(config.location_assignment.clone()),
                ));
            }
        }

        // Check that the initial variable constraint is satisfied
        for var_constr in self.ta.initial_variable_conditions() {
            if !var_constr
                .check_satisfied(&config.variable_assignment, &self.parameter_assignment)
                .map_err(PathBuilderError::from)?
            {
                return Err(PathBuilderError::InitialVariableConstraintNotSatisfied(
                    Box::new(var_constr.clone()),
                    Box::new(config.variable_assignment.clone()),
                ));
            }
        }

        Ok(())
    }

    /// Validate the transition and rule sequence and build the path
    pub fn build(mut self) -> Result<Path, PathBuilderError> {
        // empty path, no validation needed
        if self.configurations.is_empty() {
            return Ok(Path {
                ta: self.ta,
                parameter_assignment: self.parameter_assignment,
                configurations: self.configurations,
                transitions: self.transitions,
            });
        }
        // We shorten the error path here remove noop transitions
        self.transitions.retain(|tr| !tr.is_noop());
        // remove configurations without updates
        self.configurations.dedup();

        self.validate_path()?;

        self.shorten_path();

        Ok(Path {
            ta: self.ta,
            parameter_assignment: self.parameter_assignment,
            configurations: self.configurations,
            transitions: self.transitions,
        })
    }

    /// This function shortens an error path by combining successive
    /// applications of the same rule
    ///
    /// It does not reorder rules
    fn shorten_path(&mut self) {
        if self.configurations.len() <= 2 {
            return;
        }

        let mut new_config = vec![
            self.configurations[0].clone(),
            self.configurations[1].clone(),
        ];
        let mut new_tr = vec![self.transitions[0].clone()];

        for (tr, config) in self
            .transitions
            .iter()
            .skip(1)
            .zip(self.configurations.iter().skip(2))
        {
            let mut tr = tr.clone();

            if new_tr.last().unwrap().rule() == tr.rule() {
                tr.number_applied += new_tr.last().unwrap().number_applied;

                new_tr.pop();
                new_config.pop();
            }

            new_tr.push(tr);
            new_config.push(config.clone());
        }

        self.configurations = new_config;
        self.transitions = new_tr;

        debug_assert!(self.validate_path().is_ok());
    }

    /// Validate the path and check that it is consistent
    fn validate_path(&self) -> Result<(), PathBuilderError> {
        // Check that the number of configurations and transitions is consistent
        if self.transitions.len() + 1 != self.configurations.len() {
            return Err(PathBuilderError::InconsistentNumberOfConfigurations);
        }

        let mut it_configs = self.configurations.iter();
        let mut curr_config = it_configs.next().unwrap();

        for transition in self.transitions.iter() {
            // Check that the transition guard is enabled
            if !transition
                .rule_used
                .guard()
                .check_satisfied(&curr_config.variable_assignment, &self.parameter_assignment)
                .unwrap()
            {
                return Err(PathBuilderError::GuardNotSatisfied(
                    Box::new(curr_config.clone()),
                    Box::new(transition.clone()),
                ));
            }

            // number_applied > 1 => guard has to be satisfied throughout executing the transition,
            // i.e., the last time before next config
            if transition.number_applied > 1 {
                let mut transition_with_reduced_counter = transition.clone();
                transition_with_reduced_counter.number_applied -= 1;
                let last_config = curr_config.apply_rule(&transition_with_reduced_counter);
                if last_config.is_none() {
                    return Err(PathBuilderError::NotEnoughProcesses(
                        Box::new(curr_config.clone()),
                        Box::new(transition.clone()),
                    ));
                }
                let last_config = last_config.unwrap();
                if !transition
                    .rule_used
                    .guard()
                    .check_satisfied(&last_config.variable_assignment, &self.parameter_assignment)
                    .unwrap()
                {
                    return Err(PathBuilderError::GuardNotSatisfied(
                        Box::new(curr_config.clone()),
                        Box::new(transition.clone()),
                    ));
                }
            }

            let next_config = it_configs.next().unwrap();

            let calculated_config = curr_config.apply_rule(transition);
            if calculated_config.is_none() {
                return Err(PathBuilderError::NotEnoughProcesses(
                    Box::new(curr_config.clone()),
                    Box::new(transition.clone()),
                ));
            }
            let calculated_config = calculated_config.unwrap();

            if calculated_config != *next_config {
                return Err(PathBuilderError::InconsistentTransition {
                    config: Box::new(curr_config.clone()),
                    tr: Box::new(transition.clone()),
                    expected_config: Box::new(next_config.clone()),
                    next_config: Box::new(calculated_config),
                });
            }

            curr_config = next_config;
        }

        Ok(())
    }
}

/// Error that can occur when building a path using a [`PathBuilder`]
#[derive(Debug, Clone, PartialEq)]
pub enum PathBuilderError {
    /// The parameter assignment does not satisfy the resilience conditions
    ResilienceConditionNotSatisfied(
        Box<BooleanExpression<Parameter>>,
        Box<HashMap<Parameter, u32>>,
    ),
    /// A parameter is missing in the parameter assignment
    MissingParameter(Parameter),
    /// The location assignment does not satisfy the resilience conditions
    InitialLocationConstraintNotSatisfied(
        Box<BooleanExpression<Location>>,
        Box<HashMap<Location, u32>>,
    ),
    /// A location is missing in the location assignment
    MissingLocation(Location),
    /// The variable assignment does not satisfy the variable conditions
    InitialVariableConstraintNotSatisfied(
        Box<BooleanExpression<Variable>>,
        Box<HashMap<Variable, u32>>,
    ),
    /// A variable is missing in the variable assignment
    MissingVariable(Variable),
    /// The number of processes is inconsistent between configurations
    InconsistentNumberOfProcesses {
        /// Number of processes in the initial configuration
        initial_n: u32,
        /// Number of processes in the current configuration
        config_n: u32,
    },
    /// An unknown rule was used in a transition
    UnknownRule(Rule),
    /// Inconsistent number of configurations and rules
    InconsistentNumberOfConfigurations,
    /// Inconsistent transition
    InconsistentTransition {
        /// Configuration involved in the transition
        config: Box<Configuration>,
        /// Transition that was applied
        tr: Box<Transition>,
        /// Expected configuration that was supplied to the builder
        expected_config: Box<Configuration>,
        /// Next configuration that was computed by applying the transition
        next_config: Box<Configuration>,
    },
    /// Guard of rule not satisfied
    GuardNotSatisfied(Box<Configuration>, Box<Transition>),
    /// Not enough processes to apply transition
    NotEnoughProcesses(Box<Configuration>, Box<Transition>),
}

impl error::Error for PathBuilderError {}

impl fmt::Display for PathBuilderError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "Error building path: ")?;
        match self {
            PathBuilderError::ResilienceConditionNotSatisfied(rc, assignment) => {
                write!(
                    f,
                    "Resilience condition {} not satisfied with assignment {}",
                    rc,
                    display_assignment(*assignment.clone())
                )
            }
            PathBuilderError::MissingParameter(p) => {
                write!(f, "Parameter assignment is missing parameter {p}")
            }
            PathBuilderError::InitialLocationConstraintNotSatisfied(constr, assignment) => {
                write!(
                    f,
                    "Initial location constraint {} not satisfied with assignment {}",
                    constr,
                    display_assignment(*assignment.clone())
                )
            }
            PathBuilderError::MissingLocation(loc) => {
                write!(f, "Location assignment is missing location {loc}")
            }
            PathBuilderError::InitialVariableConstraintNotSatisfied(constr, assignment) => {
                write!(
                    f,
                    "Initial variable constraint {} not satisfied with assignment {}",
                    constr,
                    display_assignment(*assignment.clone())
                )
            }
            PathBuilderError::MissingVariable(variable) => {
                write!(f, "Variable assignment is missing variable {variable}")
            }
            PathBuilderError::InconsistentNumberOfProcesses {
                initial_n,
                config_n,
            } => {
                write!(
                    f,
                    "Inconsistent number of processes: expected {initial_n} but got {config_n}"
                )
            }
            PathBuilderError::UnknownRule(rule) => {
                write!(f, "Unknown rule appears in the transition: {rule}")
            }
            PathBuilderError::InconsistentNumberOfConfigurations => {
                write!(
                    f,
                    "Inconsistent number of configurations and rules were supplied to the path builder"
                )
            }
            PathBuilderError::InconsistentTransition {
                config,
                tr,
                expected_config,
                next_config,
            } => {
                write!(
                    f,
                    "Inconsistent transition: configuration {config} with transition {tr} does not lead to the expected configuration {expected_config} but to {next_config}"
                )
            }
            PathBuilderError::GuardNotSatisfied(config, tr) => {
                write!(
                    f,
                    "Tried to apply rule {} to configuration {}, but the guard is not satisfied",
                    tr.rule_used, config
                )
            }
            PathBuilderError::NotEnoughProcesses(config, tr) => {
                write!(
                    f,
                    "Tried to apply rule {} to configuration {}, but there are not enough processes in the source  location",
                    tr.rule_used.id(),
                    config
                )
            }
        }
    }
}

/// Display a an assignment for example of parameters, locations or variables
fn display_assignment<K: fmt::Display + hash::Hash + Eq, V: fmt::Display>(
    map: HashMap<K, V>,
) -> String {
    let mut keys = map.keys().collect::<Vec<_>>();
    keys.sort_by_key(|k| k.to_string());
    join_iterator(
        keys.into_iter().map(|k| format!("{} : {}", k, map[k])),
        ", ",
    )
}

impl From<EvaluationError<Parameter>> for PathBuilderError {
    fn from(err: EvaluationError<Parameter>) -> Self {
        match err {
            EvaluationError::AtomicNotFound(p) | EvaluationError::ParameterNotFound(p) => {
                PathBuilderError::MissingParameter(p)
            }
        }
    }
}

impl From<EvaluationError<Location>> for PathBuilderError {
    fn from(err: EvaluationError<Location>) -> Self {
        match err {
            EvaluationError::AtomicNotFound(l) => PathBuilderError::MissingLocation(l),
            EvaluationError::ParameterNotFound(p) => PathBuilderError::MissingParameter(p),
        }
    }
}

impl From<EvaluationError<Variable>> for PathBuilderError {
    fn from(err: EvaluationError<Variable>) -> Self {
        match err {
            EvaluationError::AtomicNotFound(v) => PathBuilderError::MissingVariable(v),
            EvaluationError::ParameterNotFound(p) => PathBuilderError::MissingParameter(p),
        }
    }
}

impl fmt::Display for Configuration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut locs = self.location_assignment.keys().collect::<Vec<_>>();
        locs.sort_by_key(|loc| loc.name());
        let locs = join_iterator(
            locs.into_iter()
                .map(|loc| format!("{} : {}", loc.name(), self.location_assignment[loc])),
            ", ",
        );

        let mut vars = self.variable_assignment.keys().collect::<Vec<_>>();
        vars.sort_by_key(|var| var.name());
        let vars = join_iterator(
            vars.into_iter()
                .map(|var| format!("{} : {}", var.name(), self.variable_assignment[var])),
            ", ",
        );

        write!(f, "locations: ({locs}), variables: ({vars})")
    }
}

impl fmt::Display for Transition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "rule: {} applied {} times",
            self.rule_used.id(),
            self.number_applied
        )
    }
}

impl fmt::Display for Path {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        debug_assert!(self.configurations.len() == self.transitions.len() + 1);

        writeln!(f, "Path of threshold automaton {}: ", self.ta.name())?;

        let param = display_assignment(self.parameter_assignment.clone());
        writeln!(f, "parameters: {param}")?;

        let mut it_transitions = self.transitions.iter();
        for (n_config, config) in self.configurations.iter().enumerate() {
            writeln!(f, "Configuration {n_config}: {config}")?;
            if let Some(transition) = it_transitions.next() {
                writeln!(f, "        |",)?;
                writeln!(f, "        |{transition}")?;
                writeln!(f, "        V")?;
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{
        BooleanVarConstraint, LocationConstraint, ParameterConstraint,
        expressions::{BooleanExpression, ComparisonOp, IntegerExpression, IntegerOp},
        general_threshold_automaton::{
            Action,
            builder::{GeneralThresholdAutomatonBuilder, RuleBuilder},
        },
    };

    use super::*;

    lazy_static::lazy_static! {
        static ref TEST_TA: GeneralThresholdAutomaton = {
            GeneralThresholdAutomatonBuilder::new("test_ta1")
            .with_parameters(vec![
                Parameter::new("n"),
                Parameter::new("t"),
                Parameter::new("f"),
            ])
            .unwrap()
            .with_variables(vec![
                Variable::new("var1"),
                Variable::new("var2"),
                Variable::new("var3"),
            ])
            .unwrap()
            .with_locations(vec![
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
            ])
            .unwrap()
            .initialize()
            .with_initial_variable_constraints(vec![BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            )])
            .unwrap()
            .with_initial_location_constraints(vec![
                LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                    ComparisonOp::Eq,
                    Box::new(
                        IntegerExpression::Param(Parameter::new("n"))
                            - IntegerExpression::Param(Parameter::new("f")),
                    ),
                ) & LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ])
            .unwrap()
            .with_resilience_conditions(vec![ParameterConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::Const(3)),
                    IntegerOp::Mul,
                    Box::new(IntegerExpression::Atom(Parameter::new("f"))),
                )),
            )])
            .unwrap()
            .with_rules(vec![
                RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2"))
                    .with_actions(vec![Action::new(
                        Variable::new("var1"),
                        IntegerExpression::Atom(Variable::new("var1")),
                    )
                    .unwrap()])
                    .build(),
                RuleBuilder::new(1, Location::new("loc2"), Location::new("loc3"))
                    .with_guard(
                        BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Const(1)),
                        ) & BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Param(Parameter::new("n")) - IntegerExpression::Const(2)),
                        ),
                    )
                    .with_actions(vec![
                        Action::new(Variable::new("var3"), IntegerExpression::Const(0)).unwrap(),
                        Action::new(
                            Variable::new("var1"),
                            IntegerExpression::BinaryExpr(
                                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                                IntegerOp::Add,
                                Box::new(IntegerExpression::Const(1)),
                            ),
                        )
                        .unwrap(),
                    ])
                    .build(),
                    RuleBuilder::new(2, Location::new("loc3"), Location::new("loc3"))
                    .with_guard(
                        BooleanVarConstraint::True,
                    )
                    .with_actions(vec![
                        Action::new(
                            Variable::new("var1"),
                            IntegerExpression::BinaryExpr(
                                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                                IntegerOp::Add,
                                Box::new(-IntegerExpression::Const(1)),
                            ),
                        )
                        .unwrap(),
                    ])
                    .build(),
            ])
            .unwrap()
            .build()
        };
    }

    #[test]
    fn test_configuration_getters() {
        let config = Configuration {
            variable_assignment: HashMap::from([
                (Variable::new("var1"), 1),
                (Variable::new("var2"), 2),
            ]),

            location_assignment: HashMap::from([
                (Location::new("loc1"), 1),
                (Location::new("loc2"), 2),
            ]),
        };

        let got_var_assignment: HashMap<_, _> = config
            .variable_assignment()
            .map(|(x, y)| (x.clone(), *y))
            .collect();
        assert_eq!(
            got_var_assignment,
            HashMap::from([(Variable::new("var1"), 1), (Variable::new("var2"), 2),])
        );

        let got_loc_assignment: HashMap<_, _> = config
            .location_assignment()
            .map(|(x, y)| (x.clone(), *y))
            .collect();
        assert_eq!(
            got_loc_assignment,
            HashMap::from([(Location::new("loc1"), 1), (Location::new("loc2"), 2),])
        );
    }

    #[test]
    fn test_display_configuration() {
        let config = Configuration {
            variable_assignment: HashMap::from([
                (Variable::new("var1"), 1),
                (Variable::new("var2"), 2),
            ]),

            location_assignment: HashMap::from([
                (Location::new("loc1"), 1),
                (Location::new("loc2"), 2),
            ]),
        };

        assert_eq!(
            format!("{config}"),
            "locations: (loc1 : 1, loc2 : 2), variables: (var1 : 1, var2 : 2)"
        );
    }

    #[test]
    fn test_display_compact_configuration() {
        let config = Configuration {
            variable_assignment: HashMap::from([
                (Variable::new("var1"), 1),
                (Variable::new("var2"), 2),
                (Variable::new("var3"), 0),
            ]),

            location_assignment: HashMap::from([
                (Location::new("loc1"), 1),
                (Location::new("loc2"), 2),
                (Location::new("loc3"), 0),
            ]),
        };

        assert_eq!(
            config.display_compact(),
            "locations: (loc1 : 1, loc2 : 2), variables: (var1 : 1, var2 : 2)"
        );
    }

    #[test]
    fn test_display_rule() {
        let rule1 = RuleBuilder::new(1, Location::new("loc1"), Location::new("loc2"))
            .with_guard(BooleanExpression::True)
            .build();

        let transition = Transition {
            rule_used: rule1.clone(),
            number_applied: 1,
        };

        assert_eq!(format!("{transition}"), "rule: 1 applied 1 times");
    }

    #[test]
    fn test_display_path() {
        let ta = TEST_TA.clone();

        let path = Path {
            ta: ta.clone(),
            parameter_assignment: [(Parameter::new("n"), 4), (Parameter::new("t"), 2)]
                .iter()
                .cloned()
                .collect(),
            configurations: vec![
                Configuration {
                    variable_assignment: [(Variable::new("var1"), 1), (Variable::new("var2"), 2)]
                        .into(),
                    location_assignment: [(Location::new("loc1"), 3), (Location::new("loc2"), 0)]
                        .into(),
                },
                Configuration {
                    variable_assignment: [(Variable::new("var1"), 1), (Variable::new("var2"), 2)]
                        .into(),
                    location_assignment: [(Location::new("loc1"), 2), (Location::new("loc2"), 1)]
                        .into(),
                },
                Configuration {
                    variable_assignment: [(Variable::new("var1"), 2), (Variable::new("var2"), 2)]
                        .into(),
                    location_assignment: [(Location::new("loc1"), 2), (Location::new("loc3"), 1)]
                        .into(),
                },
            ],
            transitions: vec![
                Transition {
                    rule_used: ta.rules().find(|r| r.id() == 0).unwrap().clone(),
                    number_applied: 1,
                },
                Transition {
                    rule_used: ta.rules().find(|r| r.id() == 1).unwrap().clone(),
                    number_applied: 1,
                },
            ],
        };

        assert_eq!(
            format!("{path}"),
            "Path of threshold automaton test_ta1: \nparameters: n : 4, t : 2\nConfiguration 0: locations: (loc1 : 3, loc2 : 0), variables: (var1 : 1, var2 : 2)\n        |\n        |rule: 0 applied 1 times\n        V\nConfiguration 1: locations: (loc1 : 2, loc2 : 1), variables: (var1 : 1, var2 : 2)\n        |\n        |rule: 1 applied 1 times\n        V\nConfiguration 2: locations: (loc1 : 2, loc3 : 1), variables: (var1 : 2, var2 : 2)\n"
        );
    }

    #[test]
    fn test_display_compact_path() {
        let ta = TEST_TA.clone();

        let path = Path {
            ta: ta.clone(),
            parameter_assignment: [(Parameter::new("n"), 5), (Parameter::new("t"), 2)].into(),
            configurations: vec![
                Configuration {
                    variable_assignment: [
                        (Variable::new("var0"), 0),
                        (Variable::new("var1"), 1),
                        (Variable::new("var2"), 2),
                    ]
                    .into(),
                    location_assignment: [
                        (Location::new("loc1"), 3),
                        (Location::new("loc2"), 1),
                        (Location::new("loc3"), 0),
                    ]
                    .into(),
                },
                Configuration {
                    variable_assignment: [
                        (Variable::new("var0"), 0),
                        (Variable::new("var1"), 1),
                        (Variable::new("var2"), 2),
                    ]
                    .into(),
                    location_assignment: [
                        (Location::new("loc1"), 1),
                        (Location::new("loc2"), 3),
                        (Location::new("loc3"), 0),
                    ]
                    .into(),
                },
                Configuration {
                    variable_assignment: [
                        (Variable::new("var0"), 0),
                        (Variable::new("var1"), 2),
                        (Variable::new("var2"), 2),
                    ]
                    .into(),
                    location_assignment: [
                        (Location::new("loc1"), 2),
                        (Location::new("loc2"), 2),
                        (Location::new("loc3"), 0),
                    ]
                    .into(),
                },
            ],
            transitions: vec![
                Transition {
                    rule_used: ta.rules().find(|r| r.id() == 0).unwrap().clone(),
                    number_applied: 1,
                },
                Transition {
                    rule_used: ta.rules().find(|r| r.id() == 1).unwrap().clone(),
                    number_applied: 1,
                },
            ],
        };

        assert_eq!(
            path.display_compact(),
            "Path of threshold automaton test_ta1: \nparameters: n : 5, t : 2\nConfiguration 0: locations: (loc1 : 3, loc2 : 1), variables: (var1 : 1, var2 : 2)\n        |\n        |rule: 0 applied 1 times\n        V\nConfiguration 1: locations: (loc1 : 1, loc2 : 3), variables: (var1 : 1, var2 : 2)\n        |\n        |rule: 1 applied 1 times\n        V\nConfiguration 2: locations: (loc1 : 2, loc2 : 2), variables: (var1 : 2, var2 : 2)\n"
        );
    }

    #[test]
    fn test_display_transition() {
        let rule = RuleBuilder::new(1, Location::new("loc1"), Location::new("loc2"))
            .with_guard(BooleanExpression::True)
            .build();

        let transition = Transition {
            rule_used: rule.clone(),
            number_applied: 1,
        };

        assert_eq!(format!("{transition}"), "rule: 1 applied 1 times");
    }

    #[test]
    fn test_path_builder_valid() {
        let ta = TEST_TA.clone();

        let path = PathBuilder::new(ta.clone())
            .add_parameter_assignment([
                (Parameter::new("n"), 4),
                (Parameter::new("t"), 2),
                (Parameter::new("f"), 1),
            ])
            .unwrap()
            .add_configuration(Configuration {
                variable_assignment: HashMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                    (Variable::new("var3"), 0),
                ]),
                location_assignment: HashMap::from([
                    (Location::new("loc1"), 3),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 0),
                ]),
            })
            .unwrap()
            .add_transition(Transition {
                rule_used: ta.rules().find(|r| r.id() == 0).unwrap().clone(),
                number_applied: 1,
            })
            .unwrap()
            .add_configuration(Configuration {
                variable_assignment: HashMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                    (Variable::new("var3"), 0),
                ]),
                location_assignment: HashMap::from([
                    (Location::new("loc1"), 2),
                    (Location::new("loc2"), 1),
                    (Location::new("loc3"), 0),
                ]),
            })
            .unwrap()
            .add_transition(Transition {
                rule_used: ta.rules().find(|r| r.id() == 1).unwrap().clone(),
                number_applied: 1,
            })
            .unwrap()
            .add_configuration(Configuration {
                variable_assignment: HashMap::from([
                    (Variable::new("var1"), 2),
                    (Variable::new("var2"), 2),
                    (Variable::new("var3"), 0),
                ]),
                location_assignment: HashMap::from([
                    (Location::new("loc1"), 2),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 1),
                ]),
            })
            .unwrap()
            .add_transition(Transition {
                rule_used: ta.rules().find(|r| r.id() == 2).unwrap().clone(),
                number_applied: 1,
            })
            .unwrap()
            .add_configuration(Configuration {
                variable_assignment: HashMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                    (Variable::new("var3"), 0),
                ]),
                location_assignment: HashMap::from([
                    (Location::new("loc1"), 2),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 1),
                ]),
            })
            .unwrap()
            .build()
            .unwrap();

        assert_eq!(path.configurations.len(), 4);
        assert_eq!(path.transitions.len(), 3);

        assert_eq!(
            path.configurations[0].variable_assignment,
            HashMap::from([
                (Variable::new("var1"), 1),
                (Variable::new("var2"), 2),
                (Variable::new("var3"), 0),
            ])
        );
        assert_eq!(
            path.configurations[0].location_assignment,
            HashMap::from([
                (Location::new("loc1"), 3),
                (Location::new("loc2"), 0),
                (Location::new("loc3"), 0),
            ])
        );

        assert_eq!(
            path.configurations[1].variable_assignment,
            HashMap::from([
                (Variable::new("var1"), 1),
                (Variable::new("var2"), 2),
                (Variable::new("var3"), 0),
            ])
        );

        assert_eq!(
            path.configurations[1].location_assignment,
            HashMap::from([
                (Location::new("loc1"), 2),
                (Location::new("loc2"), 1),
                (Location::new("loc3"), 0),
            ])
        );

        assert_eq!(
            path.configurations[2].variable_assignment,
            HashMap::from([
                (Variable::new("var1"), 2),
                (Variable::new("var2"), 2),
                (Variable::new("var3"), 0),
            ])
        );
        assert_eq!(
            path.configurations[2].location_assignment,
            HashMap::from([
                (Location::new("loc1"), 2),
                (Location::new("loc2"), 0),
                (Location::new("loc3"), 1),
            ])
        );

        assert_eq!(
            path.configurations[3].variable_assignment,
            HashMap::from([
                (Variable::new("var1"), 1),
                (Variable::new("var2"), 2),
                (Variable::new("var3"), 0),
            ])
        );
        assert_eq!(
            path.configurations[3].location_assignment,
            HashMap::from([
                (Location::new("loc1"), 2),
                (Location::new("loc2"), 0),
                (Location::new("loc3"), 1),
            ])
        );
    }

    #[test]
    fn test_empty_path_builder() {
        let ta = TEST_TA.clone();

        let path = PathBuilder::new(ta.clone())
            .add_parameter_assignment([
                (Parameter::new("n"), 4),
                (Parameter::new("t"), 2),
                (Parameter::new("f"), 1),
            ])
            .unwrap()
            .build()
            .unwrap();

        assert_eq!(path.configurations.len(), 0);
        assert_eq!(path.transitions.len(), 0);
    }

    #[test]
    fn test_path_builder_err_inconsistent_rc() {
        let ta = TEST_TA.clone();

        let path = PathBuilder::new(ta.clone()).add_parameter_assignment(HashMap::from([
            (Parameter::new("n"), 3),
            (Parameter::new("t"), 2),
            (Parameter::new("f"), 1),
        ]));

        assert!(path.is_err());
        let err = path.unwrap_err();
        assert!(
            matches!(err, PathBuilderError::ResilienceConditionNotSatisfied(_, _)),
            "got error instead {err}"
        );
        assert!(err.to_string().contains("Resilience condition"));
        assert!(
            err.to_string().contains(
                &ParameterConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Parameter::new("n"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::BinaryExpr(
                        Box::new(IntegerExpression::Const(3)),
                        IntegerOp::Mul,
                        Box::new(IntegerExpression::Atom(Parameter::new("f"))),
                    )),
                )
                .to_string()
            )
        );
    }

    #[test]
    fn test_path_builder_err_missing_param() {
        let ta = TEST_TA.clone();

        // parameter missing from assignment
        let path = PathBuilder::new(ta.clone()).add_parameter_assignment(HashMap::from([
            (Parameter::new("n"), 4),
            (Parameter::new("t"), 2),
        ]));

        assert!(path.is_err());
        let err = path.unwrap_err();
        assert!(
            matches!(err, PathBuilderError::MissingParameter(_)),
            "got error instead {err}"
        );
        assert!(err.to_string().contains("missing parameter"));
        assert!(err.to_string().contains(&Parameter::new("f").to_string()));
    }

    #[test]
    fn test_path_builder_err_init_loc_constr() {
        let ta = TEST_TA.clone();

        // initial location constraint not satisfied
        let path = PathBuilder::new(ta.clone())
            .add_parameter_assignment(HashMap::from([
                (Parameter::new("n"), 4),
                (Parameter::new("t"), 2),
                (Parameter::new("f"), 1),
            ]))
            .unwrap()
            .add_configuration(Configuration {
                variable_assignment: HashMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                    (Variable::new("var3"), 0),
                ]),
                location_assignment: HashMap::from([
                    (Location::new("loc1"), 1),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 0),
                ]),
            });

        assert!(path.is_err());
        let err = path.unwrap_err();
        assert!(
            matches!(
                err,
                PathBuilderError::InitialLocationConstraintNotSatisfied(_, _)
            ),
            "got error instead {err}"
        );
        assert!(err.to_string().contains("Initial location constraint"));
        assert!(
            err.to_string().contains(
                &LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                    ComparisonOp::Eq,
                    Box::new(
                        IntegerExpression::Param(Parameter::new("n"))
                            - IntegerExpression::Param(Parameter::new("f")),
                    ),
                )
                .to_string()
            )
        );
    }

    #[test]
    fn test_path_builder_err_loc_missing() {
        let ta = TEST_TA.clone();

        // location missing from assignment
        let path = PathBuilder::new(ta.clone())
            .add_parameter_assignment(HashMap::from([
                (Parameter::new("n"), 4),
                (Parameter::new("t"), 2),
                (Parameter::new("f"), 1),
            ]))
            .unwrap()
            .add_configuration(Configuration {
                variable_assignment: HashMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                    (Variable::new("var3"), 0),
                ]),
                location_assignment: HashMap::from([
                    (Location::new("loc1"), 2),
                    (Location::new("loc3"), 0),
                ]),
            });

        assert!(path.is_err());
        let err = path.unwrap_err();
        assert!(
            matches!(err, PathBuilderError::MissingLocation(_)),
            "got error instead {err}"
        );
        assert!(err.to_string().contains("missing location"));
        assert!(err.to_string().contains(&Location::new("loc2").to_string()));
    }

    #[test]
    fn test_path_builder_err_init_var_constr() {
        let ta = TEST_TA.clone();
        // initial variable constraint not satisfied
        let path = PathBuilder::new(ta.clone())
            .add_parameter_assignment(HashMap::from([
                (Parameter::new("n"), 4),
                (Parameter::new("t"), 2),
                (Parameter::new("f"), 1),
            ]))
            .unwrap()
            .add_configuration(Configuration {
                variable_assignment: HashMap::from([
                    (Variable::new("var1"), 2),
                    (Variable::new("var2"), 2),
                    (Variable::new("var3"), 0),
                ]),
                location_assignment: HashMap::from([
                    (Location::new("loc1"), 3),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 1),
                ]),
            });

        assert!(path.is_err());
        let err = path.unwrap_err();
        assert!(
            matches!(
                err,
                PathBuilderError::InitialVariableConstraintNotSatisfied(_, _)
            ),
            "got error instead {err}"
        );
        assert!(err.to_string().contains("Initial variable constraint"));
    }

    #[test]
    fn test_path_builder_err_var_missing() {
        let ta = TEST_TA.clone();
        // variable missing from assignment
        let path = PathBuilder::new(ta.clone())
            .add_parameter_assignment(HashMap::from([
                (Parameter::new("n"), 4),
                (Parameter::new("t"), 2),
                (Parameter::new("f"), 1),
            ]))
            .unwrap()
            .add_configuration(Configuration {
                variable_assignment: HashMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                ]),
                location_assignment: HashMap::from([
                    (Location::new("loc1"), 2),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 1),
                ]),
            });

        assert!(path.is_err());
        let err = path.unwrap_err();
        assert!(
            matches!(err, PathBuilderError::MissingVariable(_)),
            "got error instead {err}"
        );
        assert!(err.to_string().contains("missing variable"));
        assert!(err.to_string().contains(&Variable::new("var3").to_string()));
    }

    #[test]
    fn test_path_builder_err_inconsistent_n_proc() {
        let ta = TEST_TA.clone();
        // inconsistent number of processes
        let path = PathBuilder::new(ta.clone())
            .add_parameter_assignment(HashMap::from([
                (Parameter::new("n"), 4),
                (Parameter::new("t"), 2),
                (Parameter::new("f"), 1),
            ]))
            .unwrap()
            .add_configuration(Configuration {
                variable_assignment: HashMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                    (Variable::new("var3"), 0),
                ]),
                location_assignment: HashMap::from([
                    (Location::new("loc1"), 3),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 0),
                ]),
            })
            .unwrap()
            .add_transition(Transition {
                rule_used: ta.rules().find(|r| r.id() == 0).unwrap().clone(),
                number_applied: 1,
            })
            .unwrap()
            .add_configuration(Configuration {
                variable_assignment: HashMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                    (Variable::new("var3"), 0),
                ]),
                location_assignment: HashMap::from([
                    (Location::new("loc1"), 2),
                    (Location::new("loc2"), 5),
                    (Location::new("loc3"), 0),
                ]),
            });

        assert!(path.is_err());
        let err = path.unwrap_err();
        assert!(
            matches!(err, PathBuilderError::InconsistentNumberOfProcesses { .. }),
            "got error instead {err}"
        );
        assert!(err.to_string().contains("Inconsistent number of processes"));
        assert!(err.to_string().contains("expected 3 but got 7"));
    }

    #[test]
    fn test_path_builder_err_not_enough_proc() {
        let ta = TEST_TA.clone();
        // inconsistent number of processes
        let path = PathBuilder::new(ta.clone())
            .add_parameter_assignment(HashMap::from([
                (Parameter::new("n"), 4),
                (Parameter::new("t"), 2),
                (Parameter::new("f"), 1),
            ]))
            .unwrap()
            .add_configuration(Configuration {
                variable_assignment: HashMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                    (Variable::new("var3"), 0),
                ]),
                location_assignment: HashMap::from([
                    (Location::new("loc1"), 3),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 0),
                ]),
            })
            .unwrap()
            .add_transition(Transition {
                rule_used: ta.rules().find(|r| r.id() == 0).unwrap().clone(),
                number_applied: 4,
            })
            .unwrap()
            .add_configuration(Configuration {
                variable_assignment: HashMap::from([
                    (Variable::new("var1"), 0),
                    (Variable::new("var2"), 4),
                    (Variable::new("var3"), 0),
                ]),
                location_assignment: HashMap::from([
                    (Location::new("loc1"), 0),
                    (Location::new("loc2"), 3),
                    (Location::new("loc3"), 0),
                ]),
            })
            .unwrap()
            .build();

        assert!(path.is_err());
        let err = path.unwrap_err();
        assert!(
            matches!(err, PathBuilderError::NotEnoughProcesses(_, _)),
            "got error instead {err}"
        );
    }

    #[test]
    fn test_path_guard_not_sat() {
        let ta = TEST_TA.clone();
        // inconsistent number of processes
        let path = PathBuilder::new(ta.clone())
            .add_parameter_assignment(HashMap::from([
                (Parameter::new("n"), 4),
                (Parameter::new("t"), 2),
                (Parameter::new("f"), 1),
            ]))
            .unwrap()
            .add_configuration(Configuration {
                variable_assignment: HashMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                    (Variable::new("var3"), 0),
                ]),
                location_assignment: HashMap::from([
                    (Location::new("loc1"), 3),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 0),
                ]),
            })
            .unwrap()
            .add_transition(Transition {
                rule_used: ta.rules().find(|r| r.id() == 0).unwrap().clone(),
                number_applied: 2,
            })
            .unwrap()
            .add_configuration(Configuration {
                variable_assignment: HashMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                    (Variable::new("var3"), 0),
                ]),
                location_assignment: HashMap::from([
                    (Location::new("loc1"), 1),
                    (Location::new("loc2"), 2),
                    (Location::new("loc3"), 0),
                ]),
            })
            .unwrap()
            .add_transition(Transition {
                rule_used: ta.rules().find(|r| r.id() == 1).unwrap().clone(),
                number_applied: 2,
            })
            .unwrap()
            .add_configuration(Configuration {
                variable_assignment: HashMap::from([
                    (Variable::new("var1"), 3),
                    (Variable::new("var2"), 2),
                    (Variable::new("var3"), 0),
                ]),
                location_assignment: HashMap::from([
                    (Location::new("loc1"), 1),
                    (Location::new("loc2"), 1),
                    (Location::new("loc3"), 1),
                ]),
            })
            .unwrap()
            .build();

        assert!(path.is_err());
        let err = path.unwrap_err();
        assert!(
            matches!(err, PathBuilderError::GuardNotSatisfied(_, _)),
            "got error instead {err}"
        );
    }

    #[test]
    fn test_builder_err_unknown_rule() {
        let ta = TEST_TA.clone();
        // unknown rule
        let path = PathBuilder::new(ta.clone())
            .add_parameter_assignment(HashMap::from([
                (Parameter::new("n"), 4),
                (Parameter::new("t"), 2),
                (Parameter::new("f"), 1),
            ]))
            .unwrap()
            .add_configuration(Configuration {
                variable_assignment: HashMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                    (Variable::new("var3"), 0),
                ]),
                location_assignment: HashMap::from([
                    (Location::new("loc1"), 3),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 0),
                ]),
            })
            .unwrap()
            .add_transition(Transition {
                rule_used: RuleBuilder::new(42, Location::new("loc1"), Location::new("loc2"))
                    .build(),
                number_applied: 1,
            });

        assert!(path.is_err());
        let err = path.unwrap_err();
        assert!(
            matches!(err, PathBuilderError::UnknownRule(_)),
            "got error instead {err}"
        );
        assert!(err.to_string().contains("Unknown rule"));
        assert!(
            err.to_string().contains(
                &RuleBuilder::new(42, Location::new("loc1"), Location::new("loc2"))
                    .build()
                    .to_string()
            )
        );
    }

    #[test]
    fn test_builder_err_inconsistent_number_cfgs() {
        let ta = TEST_TA.clone();

        let path = PathBuilder::new(ta.clone())
            .add_parameter_assignment(HashMap::from([
                (Parameter::new("n"), 4),
                (Parameter::new("t"), 2),
                (Parameter::new("f"), 1),
            ]))
            .unwrap()
            .add_configuration(Configuration {
                variable_assignment: HashMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                    (Variable::new("var3"), 0),
                ]),
                location_assignment: HashMap::from([
                    (Location::new("loc1"), 3),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 0),
                ]),
            })
            .unwrap()
            .add_configuration(Configuration {
                variable_assignment: HashMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                    (Variable::new("var3"), 0),
                ]),
                location_assignment: HashMap::from([
                    (Location::new("loc1"), 1),
                    (Location::new("loc2"), 2),
                    (Location::new("loc3"), 0),
                ]),
            })
            .unwrap()
            .build();

        assert!(path.is_err());
        let err = path.unwrap_err();
        assert!(
            matches!(err, PathBuilderError::InconsistentNumberOfConfigurations),
            "got error instead {err}"
        );
        assert!(
            err.to_string()
                .contains("Inconsistent number of configurations")
        );
    }

    #[test]
    fn test_builder_err_inconsistent_transition() {
        let ta = TEST_TA.clone();

        let path = PathBuilder::new(ta.clone())
            .add_parameter_assignment(HashMap::from([
                (Parameter::new("n"), 4),
                (Parameter::new("t"), 2),
                (Parameter::new("f"), 1),
            ]))
            .unwrap()
            .add_configuration(Configuration {
                variable_assignment: HashMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                    (Variable::new("var3"), 0),
                ]),
                location_assignment: HashMap::from([
                    (Location::new("loc1"), 3),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 0),
                ]),
            })
            .unwrap()
            .add_transition(Transition {
                rule_used: ta.rules().find(|r| r.id() == 0).unwrap().clone(),
                number_applied: 1,
            })
            .unwrap()
            .add_configuration(Configuration {
                variable_assignment: HashMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                    (Variable::new("var3"), 0),
                ]),
                location_assignment: HashMap::from([
                    (Location::new("loc1"), 2),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 1),
                ]),
            })
            .unwrap()
            .build();

        assert!(
            path.is_err(),
            "expected error because of inconsistent transition"
        );
        let err = path.unwrap_err();
        assert!(
            matches!(err, PathBuilderError::InconsistentTransition { .. }),
            "got error instead {err}"
        );
        assert!(err.to_string().contains("Inconsistent transition"));

        assert!(
            err.to_string().contains(
                &Configuration {
                    variable_assignment: HashMap::from([
                        (Variable::new("var1"), 1),
                        (Variable::new("var2"), 2),
                        (Variable::new("var3"), 0),
                    ]),
                    location_assignment: HashMap::from([
                        (Location::new("loc1"), 2),
                        (Location::new("loc2"), 0),
                        (Location::new("loc3"), 1),
                    ]),
                }
                .to_string()
            )
        );

        assert!(
            err.to_string().contains(
                &Transition {
                    rule_used: ta.rules().find(|r| r.id() == 0).unwrap().clone(),
                    number_applied: 1,
                }
                .to_string()
            )
        );

        assert!(
            err.to_string().contains(
                &Configuration {
                    variable_assignment: HashMap::from([
                        (Variable::new("var1"), 1),
                        (Variable::new("var2"), 2),
                        (Variable::new("var3"), 0),
                    ]),
                    location_assignment: HashMap::from([
                        (Location::new("loc1"), 3),
                        (Location::new("loc2"), 0),
                        (Location::new("loc3"), 0),
                    ]),
                }
                .to_string()
            )
        );
    }

    #[test]
    fn test_builder_err_not_enough_processes() {
        let ta = TEST_TA.clone();

        let path = PathBuilder::new(ta.clone())
            .add_parameter_assignment(HashMap::from([
                (Parameter::new("n"), 4),
                (Parameter::new("t"), 2),
                (Parameter::new("f"), 1),
            ]))
            .unwrap()
            .add_configuration(Configuration {
                variable_assignment: HashMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                    (Variable::new("var3"), 0),
                ]),
                location_assignment: HashMap::from([
                    (Location::new("loc1"), 3),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 0),
                ]),
            })
            .unwrap()
            .add_transition(Transition {
                rule_used: ta.rules().find(|r| r.id() == 1).unwrap().clone(),
                number_applied: 1,
            })
            .unwrap()
            .add_configuration(Configuration {
                variable_assignment: HashMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                    (Variable::new("var3"), 0),
                ]),
                location_assignment: HashMap::from([
                    (Location::new("loc1"), 2),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 1),
                ]),
            })
            .unwrap()
            .build();

        assert!(
            path.is_err(),
            "expected error because not enough processes to apply rule"
        );
        let err = path.unwrap_err();
        assert!(
            matches!(err, PathBuilderError::NotEnoughProcesses(_, _)),
            "got error instead {err}"
        );
        assert!(err.to_string().contains("not enough processes"));
    }

    #[test]
    fn test_builder_err_not_enough_processes_multi_apply() {
        let ta = TEST_TA.clone();

        let path = PathBuilder::new(ta.clone())
            .add_parameter_assignment(HashMap::from([
                (Parameter::new("n"), 5),
                (Parameter::new("t"), 2),
                (Parameter::new("f"), 1),
            ]))
            .unwrap()
            .add_configuration(Configuration {
                variable_assignment: HashMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                    (Variable::new("var3"), 0),
                ]),
                location_assignment: HashMap::from([
                    (Location::new("loc1"), 4),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 0),
                ]),
            })
            .unwrap()
            .add_transition(Transition {
                rule_used: ta.rules().find(|r| r.id() == 0).unwrap().clone(),
                number_applied: 5,
            })
            .unwrap()
            .add_configuration(Configuration {
                variable_assignment: HashMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                    (Variable::new("var3"), 0),
                ]),
                location_assignment: HashMap::from([
                    (Location::new("loc1"), 0),
                    (Location::new("loc2"), 4),
                    (Location::new("loc3"), 0),
                ]),
            })
            .unwrap()
            .build();

        assert!(
            path.is_err(),
            "expected error because not enough processes to apply rule"
        );
        let err = path.unwrap_err();
        assert!(
            matches!(err, PathBuilderError::NotEnoughProcesses(_, _)),
            "got error instead {err}"
        );
        assert!(err.to_string().contains("not enough processes"));
    }

    #[test]
    fn test_builder_error_guard_not_satisfied() {
        let ta = TEST_TA.clone();

        let path = PathBuilder::new(ta.clone())
            .add_parameter_assignment([
                (Parameter::new("n"), 4),
                (Parameter::new("t"), 2),
                (Parameter::new("f"), 1),
            ])
            .unwrap()
            .add_configurations(vec![
                Configuration {
                    variable_assignment: HashMap::from([
                        (Variable::new("var1"), 1),
                        (Variable::new("var2"), 5),
                        (Variable::new("var3"), 0),
                    ]),
                    location_assignment: HashMap::from([
                        (Location::new("loc1"), 3),
                        (Location::new("loc2"), 0),
                        (Location::new("loc3"), 0),
                    ]),
                },
                Configuration {
                    variable_assignment: HashMap::from([
                        (Variable::new("var1"), 1),
                        (Variable::new("var2"), 5),
                        (Variable::new("var3"), 0),
                    ]),
                    location_assignment: HashMap::from([
                        (Location::new("loc1"), 2),
                        (Location::new("loc2"), 1),
                        (Location::new("loc3"), 0),
                    ]),
                },
                Configuration {
                    variable_assignment: HashMap::from([
                        (Variable::new("var1"), 2),
                        (Variable::new("var2"), 5),
                        (Variable::new("var3"), 0),
                    ]),
                    location_assignment: HashMap::from([
                        (Location::new("loc1"), 2),
                        (Location::new("loc2"), 0),
                        (Location::new("loc3"), 1),
                    ]),
                },
            ])
            .unwrap()
            .add_transitions(vec![
                Transition {
                    rule_used: ta.rules().find(|r| r.id() == 0).unwrap().clone(),
                    number_applied: 1,
                },
                Transition {
                    rule_used: ta.rules().find(|r| r.id() == 1).unwrap().clone(),
                    number_applied: 1,
                },
            ])
            .unwrap()
            .build();

        assert!(
            path.is_err(),
            "expected error because guard of rule not satisfied"
        );
        let err = path.unwrap_err();
        assert!(
            matches!(err, PathBuilderError::GuardNotSatisfied(_, _)),
            "got error instead {err}"
        );
        assert!(err.to_string().contains("guard is not satisfied"));
        assert!(
            err.to_string().contains(
                &ta.rules()
                    .find(|r| r.id() == 1)
                    .unwrap()
                    .clone()
                    .to_string()
            )
        );
    }

    #[test]
    fn test_from_evaluation_error_location() {
        let err = EvaluationError::AtomicNotFound(Location::new("loc1"));
        let path_err: PathBuilderError = err.into();
        assert!(matches!(path_err, PathBuilderError::MissingLocation(_)));

        let err: EvaluationError<Location> =
            EvaluationError::ParameterNotFound(Parameter::new("param1"));
        let path_err: PathBuilderError = err.into();
        assert!(matches!(path_err, PathBuilderError::MissingParameter(_)));
    }

    #[test]
    fn test_from_evaluation_error_variable() {
        let err = EvaluationError::AtomicNotFound(Variable::new("var1"));
        let path_err: PathBuilderError = err.into();
        assert!(matches!(path_err, PathBuilderError::MissingVariable(_)));

        let err: EvaluationError<Variable> =
            EvaluationError::ParameterNotFound(Parameter::new("param1"));
        let path_err: PathBuilderError = err.into();
        assert!(matches!(path_err, PathBuilderError::MissingParameter(_)));
    }

    #[test]
    fn test_apply_rule() {
        let cfg = Configuration {
            variable_assignment: HashMap::from([]),
            location_assignment: HashMap::from([
                (Location::new("loc1"), 2),
                (Location::new("loc2"), 0),
                (Location::new("loc3"), 1),
            ]),
        };

        let rule = RuleBuilder::new(1, Location::new("loc1"), Location::new("loc2"))
            .with_guard(BooleanExpression::True)
            .build();

        let trans = Transition {
            rule_used: rule,
            number_applied: 1,
        };

        let expected_cfg = Configuration {
            variable_assignment: HashMap::from([]),
            location_assignment: HashMap::from([
                (Location::new("loc1"), 1),
                (Location::new("loc2"), 1),
                (Location::new("loc3"), 1),
            ]),
        };

        assert_eq!(cfg.apply_rule(&trans), Some(expected_cfg));
    }

    #[test]
    fn test_apply_rule_self_loop_multi() {
        let cfg = Configuration {
            variable_assignment: HashMap::from([]),
            location_assignment: HashMap::from([
                (Location::new("loc1"), 2),
                (Location::new("loc2"), 0),
                (Location::new("loc3"), 1),
            ]),
        };

        let rule = RuleBuilder::new(1, Location::new("loc1"), Location::new("loc1"))
            .with_guard(BooleanExpression::True)
            .build();

        let trans = Transition {
            rule_used: rule,
            number_applied: 5,
        };

        let expected_cfg = Configuration {
            variable_assignment: HashMap::from([]),
            location_assignment: HashMap::from([
                (Location::new("loc1"), 2),
                (Location::new("loc2"), 0),
                (Location::new("loc3"), 1),
            ]),
        };

        assert_eq!(cfg.apply_rule(&trans), Some(expected_cfg));
    }

    #[test]
    fn test_apply_rule_self_loop_no_proc() {
        let cfg = Configuration {
            variable_assignment: HashMap::from([]),
            location_assignment: HashMap::from([
                (Location::new("loc1"), 2),
                (Location::new("loc2"), 0),
                (Location::new("loc3"), 1),
            ]),
        };

        let rule = RuleBuilder::new(1, Location::new("loc2"), Location::new("loc2"))
            .with_guard(BooleanExpression::True)
            .build();

        let trans = Transition {
            rule_used: rule,
            number_applied: 1,
        };

        assert_eq!(cfg.apply_rule(&trans), None);
    }

    #[test]
    fn test_apply_rule_not_enough_processes() {
        let cfg = Configuration {
            variable_assignment: HashMap::from([]),
            location_assignment: HashMap::from([
                (Location::new("loc1"), 2),
                (Location::new("loc2"), 0),
                (Location::new("loc3"), 1),
            ]),
        };

        let rule = RuleBuilder::new(1, Location::new("loc1"), Location::new("loc2"))
            .with_guard(BooleanExpression::True)
            .build();

        let trans = Transition {
            rule_used: rule,
            number_applied: 3,
        };

        assert_eq!(cfg.apply_rule(&trans), None);
    }

    #[test]
    fn test_shorten_path() {
        let ta = TEST_TA.clone();

        let path = PathBuilder::new(ta.clone())
            .add_parameter_assignment([
                (Parameter::new("n"), 4),
                (Parameter::new("t"), 2),
                (Parameter::new("f"), 1),
            ])
            .unwrap()
            .add_configurations(vec![
                Configuration {
                    variable_assignment: HashMap::from([
                        (Variable::new("var1"), 1),
                        (Variable::new("var2"), 0),
                        (Variable::new("var3"), 0),
                    ]),
                    location_assignment: HashMap::from([
                        (Location::new("loc1"), 3),
                        (Location::new("loc2"), 0),
                        (Location::new("loc3"), 0),
                    ]),
                },
                Configuration {
                    variable_assignment: HashMap::from([
                        (Variable::new("var1"), 1),
                        (Variable::new("var2"), 0),
                        (Variable::new("var3"), 0),
                    ]),
                    location_assignment: HashMap::from([
                        (Location::new("loc1"), 2),
                        (Location::new("loc2"), 1),
                        (Location::new("loc3"), 0),
                    ]),
                },
                Configuration {
                    variable_assignment: HashMap::from([
                        (Variable::new("var1"), 1),
                        (Variable::new("var2"), 0),
                        (Variable::new("var3"), 0),
                    ]),
                    location_assignment: HashMap::from([
                        (Location::new("loc1"), 1),
                        (Location::new("loc2"), 2),
                        (Location::new("loc3"), 0),
                    ]),
                },
            ])
            .unwrap()
            .add_transitions(vec![
                Transition {
                    rule_used: ta.rules().find(|r| r.id() == 0).unwrap().clone(),
                    number_applied: 1,
                },
                Transition {
                    rule_used: ta.rules().find(|r| r.id() == 0).unwrap().clone(),
                    number_applied: 1,
                },
            ])
            .unwrap()
            .build();

        assert!(
            path.is_ok(),
            "Expected path to be valid, got error {}",
            path.unwrap_err()
        );

        let got_path = path.unwrap();

        let expected_path = Path {
            ta: ta.clone(),
            parameter_assignment: HashMap::from([
                (Parameter::new("n"), 4),
                (Parameter::new("t"), 2),
                (Parameter::new("f"), 1),
            ]),
            configurations: vec![
                Configuration {
                    variable_assignment: HashMap::from([
                        (Variable::new("var1"), 1),
                        (Variable::new("var2"), 0),
                        (Variable::new("var3"), 0),
                    ]),
                    location_assignment: HashMap::from([
                        (Location::new("loc1"), 3),
                        (Location::new("loc2"), 0),
                        (Location::new("loc3"), 0),
                    ]),
                },
                Configuration {
                    variable_assignment: HashMap::from([
                        (Variable::new("var1"), 1),
                        (Variable::new("var2"), 0),
                        (Variable::new("var3"), 0),
                    ]),
                    location_assignment: HashMap::from([
                        (Location::new("loc1"), 1),
                        (Location::new("loc2"), 2),
                        (Location::new("loc3"), 0),
                    ]),
                },
            ],
            transitions: vec![Transition {
                rule_used: ta.rules().find(|r| r.id() == 0).unwrap().clone(),
                number_applied: 2,
            }],
        };

        assert_eq!(
            got_path, expected_path,
            "Got: {}\nExpected: {}",
            got_path, expected_path
        )
    }
}
