//! Factory methods for building a valid [`GeneralThresholdAutomaton`]
//!
//! This module contains the builder [`GeneralThresholdAutomatonBuilder`] for a
//! [`GeneralThresholdAutomaton`]. The builder will ensure that the threshold
//! automaton is valid, e.g., ensure that all variables in expressions are
//! declared.

use std::{
    cmp::Ordering,
    collections::{HashMap, HashSet},
    fmt::{Debug, Display},
};

use super::{
    Action, BooleanVarConstraint, GeneralThresholdAutomaton, LocationConstraint,
    ParameterConstraint, Rule, UpdateExpression,
};
use crate::{
    ThresholdAutomaton,
    expressions::{
        Atomic, BooleanExpression, IntegerExpression, IsDeclared, Location, Parameter, Variable,
        properties::EvaluationError,
    },
};

/// Builder for constructing a [`GeneralThresholdAutomaton`]
///
/// A builder can be used to construct a [`GeneralThresholdAutomaton`], ensuring
/// that the threshold automaton is valid. The builder has two stages: In the
/// first stage, parameters, variables, and locations can be added to the
/// threshold automaton. This stage is completed by calling
/// [`GeneralThresholdAutomatonBuilder::initialize`],
/// transforming the builder into an
/// [`InitializedGeneralThresholdAutomatonBuilder`].
///
/// In the second stage, rules, resilience conditions, and initial location
/// constraints are added. The threshold automaton is then constructed by calling
/// [`InitializedGeneralThresholdAutomatonBuilder::build`].
///
/// # Example
///
/// ```
/// use taco_threshold_automaton::expressions::*;
/// use taco_threshold_automaton::general_threshold_automaton::builder::*;
///
/// // Building a threshold automaton
/// let _ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
///            .with_parameter(Parameter::new("n")).unwrap()
///            .with_variable(Variable::new("var1")).unwrap()
///            .with_locations(vec![
///                Location::new("loc1"),
///                Location::new("loc2"),
///            ]).unwrap()
///            .initialize()
///            .with_rules(vec![
///                RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2")).build(),
///            ]).unwrap()
///            .build();
///
///
/// let builder = GeneralThresholdAutomatonBuilder::new("test_ta1")
///            .with_parameter(Parameter::new("n")).unwrap()
///            .with_variable(Variable::new("var1")).unwrap()
///            .with_locations(vec![
///                Location::new("loc1"),
///                Location::new("loc2"),
///                Location::new("loc3"),
///            ]).unwrap()
///            .initialize();
///
/// assert!(builder.has_parameter(&Parameter::new("n")));
/// assert!(builder.has_variable(&Variable::new("var1")));
/// assert!(builder.has_location(&Location::new("loc1")));
/// assert!(builder.has_location(&Location::new("loc2")));
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GeneralThresholdAutomatonBuilder {
    ta: GeneralThresholdAutomaton,
}

impl GeneralThresholdAutomatonBuilder {
    /// Create a new threshold automaton builder
    pub fn new(name: impl ToString) -> Self {
        GeneralThresholdAutomatonBuilder {
            ta: GeneralThresholdAutomaton {
                name: name.to_string(),
                parameters: HashSet::new(),
                variables: HashSet::new(),
                locations: HashSet::new(),
                outgoing_rules: HashMap::new(),
                initial_location_constraint: vec![],
                initial_variable_constraint: vec![],
                resilience_condition: vec![],
            },
        }
    }

    /// Checks whether a name is already present in the threshold automaton
    fn check_for_name_clash(&self, name: &str) -> bool {
        self.ta.parameters.contains(&Parameter::new(name))
            || self.ta.variables.contains(&Variable::new(name))
            || self.ta.locations.contains(&Location::new(name))
    }

    /// Adds a parameter to the threshold automaton
    ///
    /// Adds a parameter to the threshold automaton. If the parameter is already
    /// present or its name is already taken an error is returned.
    ///
    ///  # Example
    ///
    /// ```
    /// use taco_threshold_automaton::expressions::*;
    /// use taco_threshold_automaton::general_threshold_automaton::builder::*;
    ///
    /// let builder = GeneralThresholdAutomatonBuilder::new("test_ta1")
    ///            .with_parameter(Parameter::new("n")).unwrap()
    ///            .initialize();
    /// assert!(builder.has_parameter(&Parameter::new("n")));
    /// ```
    pub fn with_parameter(mut self, param: Parameter) -> Result<Self, BuilderError> {
        if self.ta.parameters.contains(&param) {
            return Err(BuilderError::DuplicateParameter(param));
        }

        if self.check_for_name_clash(param.name()) {
            return Err(BuilderError::NameClash(param.name().to_string()));
        }

        self.ta.parameters.insert(param);
        Ok(self)
    }

    /// Adds multiple parameters to the threshold automaton
    ///
    /// Adds multiple parameters to the threshold automaton. If any of the
    /// parameters are duplicates or a name is already taken an error is
    /// returned.
    ///
    ///  # Example
    ///
    /// ```
    /// use taco_threshold_automaton::expressions::*;
    /// use taco_threshold_automaton::general_threshold_automaton::builder::*;
    ///
    /// let builder = GeneralThresholdAutomatonBuilder::new("test_ta1")
    ///            .with_parameters(vec![
    ///                 Parameter::new("n"),
    ///                 Parameter::new("t")]
    ///            ).unwrap()
    ///            .initialize();
    ///
    /// assert!(builder.has_parameter(&Parameter::new("n")));
    /// assert!(builder.has_parameter(&Parameter::new("t")));
    /// ```
    pub fn with_parameters(
        self,
        params: impl IntoIterator<Item = Parameter>,
    ) -> Result<Self, BuilderError> {
        let mut res = self;
        for param in params {
            res = res.with_parameter(param)?;
        }

        Ok(res)
    }

    /// Adds a variable to the threshold automaton
    ///
    /// Adds a variable to the threshold automaton. If the variable is already
    /// present or its name is already taken an error is returned.
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::expressions::*;
    /// use taco_threshold_automaton::general_threshold_automaton::builder::*;
    ///
    /// let builder = GeneralThresholdAutomatonBuilder::new("test_ta1")
    ///           .with_variable(Variable::new("var1")).unwrap()
    ///           .initialize();
    /// assert!(builder.has_variable(&Variable::new("var1")));
    /// ```
    pub fn with_variable(mut self, var: Variable) -> Result<Self, BuilderError> {
        if self.ta.variables.contains(&var) {
            return Err(BuilderError::DuplicateVariable(var));
        }

        if self.check_for_name_clash(var.name()) {
            return Err(BuilderError::NameClash(var.name().to_string()));
        }

        self.ta.variables.insert(var);
        Ok(self)
    }

    /// Adds multiple variables to the threshold automaton
    ///
    /// Adds multiple variables to the threshold automaton. If any of the
    /// variables are duplicates or a name is already taken an error is
    /// returned.
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::expressions::*;
    /// use taco_threshold_automaton::general_threshold_automaton::builder::*;
    ///
    /// let builder = GeneralThresholdAutomatonBuilder::new("test_ta1")
    ///         .with_variables(vec![
    ///             Variable::new("var1"),
    ///             Variable::new("var2"),
    ///         ]).unwrap()
    ///         .initialize();
    ///
    /// assert!(builder.has_variable(&Variable::new("var1")));
    /// assert!(builder.has_variable(&Variable::new("var2")));
    /// ```
    pub fn with_variables(
        self,
        vars: impl IntoIterator<Item = Variable>,
    ) -> Result<Self, BuilderError> {
        let mut res = self;
        for var in vars {
            res = res.with_variable(var)?;
        }

        Ok(res)
    }

    /// Adds a location to the threshold automaton
    ///
    /// Adds a location to the threshold automaton. If the location is already
    /// present or its name is already taken an error is returned.
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::expressions::Location;
    /// use taco_threshold_automaton::general_threshold_automaton::builder::*;
    ///
    /// let builder = GeneralThresholdAutomatonBuilder::new("test_ta1")
    ///        .with_location(Location::new("loc1")).unwrap()
    ///        .initialize();
    ///
    /// assert!(builder.has_location(&Location::new("loc1")));
    /// ```
    pub fn with_location(mut self, loc: Location) -> Result<Self, BuilderError> {
        if self.ta.locations.contains(&loc) {
            return Err(BuilderError::DuplicateLocation(loc));
        }

        if self.check_for_name_clash(loc.name()) {
            return Err(BuilderError::NameClash(loc.name().to_string()));
        }

        self.ta.locations.insert(loc);
        Ok(self)
    }

    /// Adds multiple locations to the threshold automaton
    ///
    /// Adds multiple locations to the threshold automaton. If any of the
    /// locations are duplicates or a name is already taken an error is
    /// returned.
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::expressions::*;
    /// use taco_threshold_automaton::general_threshold_automaton::builder::*;
    ///
    /// let builder = GeneralThresholdAutomatonBuilder::new("test_ta1")
    ///         .with_locations(vec![
    ///             Location::new("loc1"),
    ///             Location::new("loc2"),
    ///         ]).unwrap()
    ///        .initialize();
    ///
    /// assert!(builder.has_location(&Location::new("loc1")));
    /// ```
    pub fn with_locations(
        self,
        locs: impl IntoIterator<Item = Location>,
    ) -> Result<Self, BuilderError> {
        let mut res = self;
        for loc in locs {
            res = res.with_location(loc)?;
        }

        Ok(res)
    }

    /// Completes the first stage of the builder, transforming it into an `InitializedGeneralThresholdAutomatonBuilder`.
    ///
    /// This method should be called after all parameters, variables, and locations have been added.
    pub fn initialize(self) -> InitializedGeneralThresholdAutomatonBuilder {
        InitializedGeneralThresholdAutomatonBuilder { ta: self.ta }
    }
}

/// A builder for a threshold automaton where parameters, variables, and
/// locations have already been added and are now fixed.
///
/// In this stage, rules, resilience conditions, and initial constraints
/// can be added to the threshold automaton.
///
/// # Example
///
/// ```
/// use taco_threshold_automaton::expressions::*;
/// use taco_threshold_automaton::general_threshold_automaton::builder::*;
/// use taco_threshold_automaton::LocationConstraint;
///
/// // Building a threshold automaton
/// let ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
///     .with_parameter(Parameter::new("n")).unwrap()
///     .with_variable(Variable::new("var1")).unwrap()
///     .with_locations(vec![
///          Location::new("loc1"),
///          Location::new("loc2"),
///      ]).unwrap()
///      .initialize()
///      .with_rules(vec![
///         RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2")).build(),
///       ]).unwrap()
///      .with_initial_location_constraint(
///             LocationConstraint::ComparisonExpression(
///                Box::new(IntegerExpression::Atom(Location::new("loc1"))),
///                ComparisonOp::Eq,
///                Box::new(IntegerExpression::Param(Parameter::new("n"))),
///       )).unwrap()   
///     .build();
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InitializedGeneralThresholdAutomatonBuilder {
    ta: GeneralThresholdAutomaton,
}

impl InitializedGeneralThresholdAutomatonBuilder {
    /// Checks whether the rule or rule id is already present in the threshold automaton
    ///
    /// Returns an error if the rule or rule id is already present, otherwise returns None
    fn contains_rule_or_rule_id(&self, rule: &Rule) -> Option<BuilderError> {
        for rule_vec in self.ta.outgoing_rules.values() {
            for ta_rule in rule_vec {
                if ta_rule.id == rule.id {
                    return Some(BuilderError::DuplicateRuleId(
                        Box::new(rule.clone()),
                        Box::new(ta_rule.clone()),
                    ));
                }
            }
        }

        None
    }

    /// Check whether a integer expression `int_expr` only uses components appearing in `known_atoms`
    ///
    /// Returns an error if the constraint does contain unknown components, otherwise returns None
    fn validate_integer_expr<T: Atomic>(
        &self,
        int_expr: &IntegerExpression<T>,
        known_atoms: &HashSet<T>,
    ) -> Option<BuilderError> {
        match int_expr {
            IntegerExpression::Atom(a) => {
                if known_atoms.contains(a) {
                    return None;
                }

                Some(BuilderError::UnknownComponent(a.to_string()))
            }
            IntegerExpression::Const(_) => None,
            IntegerExpression::Param(p) => {
                if !self.ta.parameters.contains(p) {
                    return Some(BuilderError::UnknownComponent(format!("Parameter {p}")));
                }

                None
            }
            IntegerExpression::BinaryExpr(lhs, _, rhs) => self
                .validate_integer_expr(lhs, known_atoms)
                .or_else(|| self.validate_integer_expr(rhs, known_atoms)),
            IntegerExpression::Neg(ex) => self.validate_integer_expr(ex, known_atoms),
        }
    }

    /// Check whether a constraint `constraint` only uses components appearing in `known_atoms`
    ///
    /// Returns an error if the constraint does contain unknown components, otherwise returns None
    fn validate_constraint<T: Atomic>(
        &self,
        constraint: &BooleanExpression<T>,
        known_atoms: &HashSet<T>,
    ) -> Option<BuilderError> {
        match constraint {
            BooleanExpression::ComparisonExpression(lhs, _, rhs) => self
                .validate_integer_expr(lhs, known_atoms)
                .or_else(|| self.validate_integer_expr(rhs, known_atoms)),
            BooleanExpression::BinaryExpression(lhs, _, rhs) => self
                .validate_constraint(lhs, known_atoms)
                .or_else(|| self.validate_constraint(rhs, known_atoms)),
            BooleanExpression::True => None,
            BooleanExpression::False => None,
            BooleanExpression::Not(b) => self.validate_constraint(b, known_atoms),
        }
    }

    /// Check whether an action is valid
    ///
    /// Returns an error if the action is invalid, otherwise returns None
    fn validate_action(&self, action: &Action) -> Option<BuilderError> {
        if !self.ta.variables.contains(&action.variable_to_update) {
            return Some(BuilderError::MalformedAction(
                Box::new(action.clone()),
                format!(
                    "Unknown Variable to update: {}, Action: {}",
                    action.variable_to_update, action
                ),
            ));
        }

        None
    }

    /// Check whether components of a rule are valid
    ///
    /// Returns an error if the rule is malformed, otherwise returns None
    fn validate_rule(&self, rule: &Rule) -> Option<BuilderError> {
        if let Some(err) = self.contains_rule_or_rule_id(rule) {
            return Some(err);
        }

        if !self.ta.locations.contains(&rule.source) {
            return Some(BuilderError::MalformedRule(
                Box::new(rule.clone()),
                format!("Source location {} not found", rule.source),
            ));
        }

        if !self.ta.locations.contains(&rule.target) {
            return Some(BuilderError::MalformedRule(
                Box::new(rule.clone()),
                format!("Target location {} not found", rule.target),
            ));
        }

        if let Some(err) = self.validate_constraint(&rule.guard, &self.ta.variables) {
            return Some(BuilderError::MalformedRule(
                Box::new(rule.clone()),
                format!("Guard constraint {} is malformed: {}", rule.guard, err),
            ));
        }

        let mut updated_variables = HashSet::new();
        for action in &rule.actions {
            // Check that variable is actually defined
            if let Some(err) = self.validate_action(action) {
                return Some(BuilderError::MalformedRule(
                    Box::new(rule.clone()),
                    format!("Action {action} is malformed: {err}"),
                ));
            }

            // Check that a single variable is not updated multiple times
            if !updated_variables.insert(action.variable_to_update.clone()) {
                return Some(BuilderError::MalformedRule(
                    Box::new(rule.clone()),
                    format!(
                        "Variable {} is updated multiple times in the same rule",
                        action.variable_to_update
                    ),
                ));
            }
        }

        None
    }

    /// Add a rule to the threshold automaton
    ///
    /// Adds a rule to the threshold automaton. It returns an error if a rule is
    /// added twice, the rule id is already taken or one of the rules
    /// expressions is invalid.
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::expressions::*;
    /// use taco_threshold_automaton::general_threshold_automaton::*;
    /// use taco_threshold_automaton::general_threshold_automaton::builder::GeneralThresholdAutomatonBuilder;
    /// use taco_threshold_automaton::general_threshold_automaton::builder::RuleBuilder;
    ///
    /// let ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
    ///     .with_locations(vec![
    ///          Location::new("loc1"),
    ///          Location::new("loc2"),
    ///      ]).unwrap()
    ///      .initialize()
    ///      .with_rule(
    ///         RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2")).build(),
    ///      ).unwrap()
    ///      .build();
    /// ```
    pub fn with_rule(mut self, rule: Rule) -> Result<Self, BuilderError> {
        if let Some(err) = self.validate_rule(&rule) {
            return Err(err);
        }

        self.ta
            .outgoing_rules
            .entry(rule.source.clone())
            .or_default()
            .push(rule.clone());

        Ok(self)
    }

    /// Add multiple rules to the threshold automaton
    ///
    /// Adds multiple rules to the threshold automaton. It returns an error if a
    /// rule is added twice, the rule id is already taken or one of the rules
    /// expressions is invalid.
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::expressions::*;
    /// use taco_threshold_automaton::general_threshold_automaton::builder::*;
    /// use taco_threshold_automaton::general_threshold_automaton::builder::GeneralThresholdAutomatonBuilder;
    ///
    /// let ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
    ///     .with_locations(vec![
    ///          Location::new("loc1"),
    ///          Location::new("loc2"),
    ///      ]).unwrap()
    ///      .initialize()
    ///      .with_rules(vec![
    ///         RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2")).build(),
    ///         RuleBuilder::new(1, Location::new("loc2"), Location::new("loc1")).build(),
    ///       ]).unwrap()
    ///     .build();
    /// ```
    pub fn with_rules(self, rules: impl IntoIterator<Item = Rule>) -> Result<Self, BuilderError> {
        let mut res = self;
        for rule in rules {
            res = res.with_rule(rule)?;
        }
        Ok(res)
    }

    /// The representation of a resilience condition is currently not unique
    /// because in this case parameters are also atoms. This function converts
    /// all atoms into parameters.
    fn canonicalize_parameter_integer_expr(
        rc: IntegerExpression<Parameter>,
    ) -> IntegerExpression<Parameter> {
        match rc {
            IntegerExpression::Atom(p) => IntegerExpression::Param(p),
            IntegerExpression::BinaryExpr(lhs, op, rhs) => IntegerExpression::BinaryExpr(
                Box::new(Self::canonicalize_parameter_integer_expr(*lhs)),
                op,
                Box::new(Self::canonicalize_parameter_integer_expr(*rhs)),
            ),
            IntegerExpression::Neg(ex) => {
                IntegerExpression::Neg(Box::new(Self::canonicalize_parameter_integer_expr(*ex)))
            }
            IntegerExpression::Const(c) => IntegerExpression::Const(c),
            IntegerExpression::Param(p) => IntegerExpression::Param(p),
        }
    }

    /// The representation of a resilience condition is currently not unique
    /// because in this case parameters are also atoms. This function converts
    /// all atoms into parameters.
    fn canonicalize_resilience_condition(rc: ParameterConstraint) -> ParameterConstraint {
        match rc {
            BooleanExpression::ComparisonExpression(lhs, op, rhs) => {
                BooleanExpression::ComparisonExpression(
                    Box::new(Self::canonicalize_parameter_integer_expr(*lhs)),
                    op,
                    Box::new(Self::canonicalize_parameter_integer_expr(*rhs)),
                )
            }
            BooleanExpression::BinaryExpression(lhs, op, rhs) => {
                BooleanExpression::BinaryExpression(
                    Box::new(Self::canonicalize_resilience_condition(*lhs)),
                    op,
                    Box::new(Self::canonicalize_resilience_condition(*rhs)),
                )
            }
            BooleanExpression::Not(ex) => {
                BooleanExpression::Not(Box::new(Self::canonicalize_resilience_condition(*ex)))
            }
            BooleanExpression::True => BooleanExpression::True,
            BooleanExpression::False => BooleanExpression::False,
        }
    }

    /// Add a resilience condition to the threshold automaton
    ///
    /// Adds a resilience condition to the threshold automaton. It returns an
    /// error if the resilience condition already exists or contains unknown
    /// parameters.
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::expressions::*;
    /// use taco_threshold_automaton::general_threshold_automaton::builder::*;
    /// use taco_threshold_automaton::ParameterConstraint;
    ///
    /// let ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
    ///     .with_parameter(Parameter::new("n")).unwrap()
    ///     .initialize()
    ///     .with_resilience_condition(
    ///         ParameterConstraint::ComparisonExpression(
    ///             Box::new(IntegerExpression::Atom(Parameter::new("n"))),
    ///             ComparisonOp::Eq,
    ///             Box::new(IntegerExpression::Const(0)),
    ///     )).unwrap()
    ///     .build();
    /// ```
    pub fn with_resilience_condition(
        mut self,
        rc: ParameterConstraint,
    ) -> Result<Self, BuilderError> {
        if let Some(err) = self.validate_constraint(&rc, &self.ta.parameters) {
            return Err(BuilderError::MalformedResilienceCondition(
                Box::new(rc.clone()),
                err.to_string(),
            ));
        }

        self.ta
            .resilience_condition
            .push(Self::canonicalize_resilience_condition(rc));
        Ok(self)
    }

    /// Add multiple resilience conditions to the threshold automaton
    ///
    /// Adds multiple resilience conditions to the threshold automaton. It
    /// returns an error if a resilience condition already exists or contains
    /// unknown parameters.
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::expressions::*;
    /// use taco_threshold_automaton::general_threshold_automaton::builder::*;
    /// use taco_threshold_automaton::ParameterConstraint;
    ///
    /// let ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
    ///    .with_parameters(vec![
    ///         Parameter::new("n"),
    ///         Parameter::new("m"),
    ///     ]).unwrap()
    ///     .initialize()
    ///     .with_resilience_conditions(vec![
    ///         ParameterConstraint::ComparisonExpression(
    ///         Box::new(IntegerExpression::Atom(Parameter::new("n"))),
    ///         ComparisonOp::Eq,
    ///         Box::new(IntegerExpression::Const(0)),
    ///     ),
    ///     ParameterConstraint::ComparisonExpression(
    ///         Box::new(IntegerExpression::Atom(Parameter::new("m"))),
    ///         ComparisonOp::Eq,
    ///         Box::new(IntegerExpression::Const(0)),
    ///     )]).unwrap()
    ///     .build();
    /// ```
    pub fn with_resilience_conditions(
        self,
        rcs: impl IntoIterator<Item = ParameterConstraint>,
    ) -> Result<Self, BuilderError> {
        let mut res = self;
        for rc in rcs {
            res = res.with_resilience_condition(rc)?;
        }
        Ok(res)
    }

    /// Add an initial location constraint to the threshold automaton
    ///
    /// Adds an initial location constraint to the threshold automaton. It
    /// returns an error if the constraint already exists or contains unknown
    /// locations.
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::expressions::*;
    /// use taco_threshold_automaton::general_threshold_automaton::builder::*;
    /// use taco_threshold_automaton::LocationConstraint;
    ///
    /// let ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
    ///     .with_location(Location::new("loc1")).unwrap()
    ///     .initialize()
    ///     .with_initial_location_constraint(
    ///         LocationConstraint::ComparisonExpression(
    ///             Box::new(IntegerExpression::Atom(Location::new("loc1"))),
    ///             ComparisonOp::Eq,
    ///             Box::new(IntegerExpression::Const(0)),
    ///     )).unwrap()
    ///     .build();
    /// ```
    pub fn with_initial_location_constraint(
        mut self,
        constraint: LocationConstraint,
    ) -> Result<Self, BuilderError> {
        if let Some(err) = self.validate_constraint(&constraint, &self.ta.locations) {
            return Err(BuilderError::MalformedInitialLocationConstraint(
                Box::new(constraint.clone()),
                err.to_string(),
            ));
        }

        self.ta.initial_location_constraint.push(constraint);
        Ok(self)
    }

    /// Add multiple initial location constraints to the threshold automaton
    ///
    /// Adds multiple initial location constraints to the threshold automaton.
    /// It returns an error if a constraint already exists or contains unknown
    /// locations.
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::ParameterConstraint;
    /// use taco_threshold_automaton::LocationConstraint;
    /// use taco_threshold_automaton::expressions::*;
    /// use taco_threshold_automaton::general_threshold_automaton::builder::*;
    ///
    /// let ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
    ///     .with_locations(vec![
    ///         Location::new("loc1"),
    ///         Location::new("loc2"),
    ///     ]).unwrap()
    ///     .initialize()
    ///     .with_initial_location_constraints(vec![
    ///         LocationConstraint::ComparisonExpression(
    ///             Box::new(IntegerExpression::Atom(Location::new("loc1"))),
    ///             ComparisonOp::Eq,
    ///             Box::new(IntegerExpression::Const(0)),
    ///         ),
    ///         LocationConstraint::ComparisonExpression(
    ///             Box::new(IntegerExpression::Atom(Location::new("loc2"))),
    ///             ComparisonOp::Eq,
    ///             Box::new(IntegerExpression::Const(0)),
    ///         ),
    ///     ]).unwrap()
    ///     .build();
    /// ```
    pub fn with_initial_location_constraints(
        self,
        constraints: impl IntoIterator<Item = LocationConstraint>,
    ) -> Result<Self, BuilderError> {
        let mut res = self;
        for constraint in constraints {
            res = res.with_initial_location_constraint(constraint)?;
        }
        Ok(res)
    }

    /// Add initial variable constraint to the threshold automaton
    ///
    /// Adds an initial variable constraint to the threshold automaton. It
    /// returns an error if the constraint already exists or contains unknown
    /// variables.
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::BooleanVarConstraint;
    /// use taco_threshold_automaton::expressions::*;
    /// use taco_threshold_automaton::general_threshold_automaton::builder::*;
    ///
    /// let ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
    ///     .with_variable(Variable::new("var1")).unwrap()
    ///     .initialize()
    ///     .with_initial_variable_constraint(
    ///         BooleanVarConstraint::ComparisonExpression(
    ///             Box::new(IntegerExpression::Atom(Variable::new("var1"))),
    ///             ComparisonOp::Eq,
    ///             Box::new(IntegerExpression::Const(0)),
    ///     )).unwrap()
    ///     .build();
    /// ```
    pub fn with_initial_variable_constraint(
        mut self,
        constraint: BooleanVarConstraint,
    ) -> Result<Self, BuilderError> {
        if let Some(err) = self.validate_constraint(&constraint, &self.ta.variables) {
            return Err(BuilderError::MalformedInitialVariableConstraint(
                Box::new(constraint.clone()),
                err.to_string(),
            ));
        }

        self.ta.initial_variable_constraint.push(constraint);
        Ok(self)
    }

    /// Add multiple initial variable constraints to the threshold automaton
    ///
    /// Adds multiple initial variable constraints to the threshold automaton.
    /// It returns an error if a constraint already exists or contains unknown
    /// variables.
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::expressions::*;
    /// use taco_threshold_automaton::BooleanVarConstraint;
    /// use taco_threshold_automaton::general_threshold_automaton::builder::*;
    ///
    /// let ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
    ///     .with_variables(vec![
    ///         Variable::new("var1"),
    ///         Variable::new("var2"),
    ///     ]).unwrap()
    ///     .initialize()
    ///     .with_initial_variable_constraints(vec![
    ///         BooleanVarConstraint::ComparisonExpression(
    ///             Box::new(IntegerExpression::Atom(Variable::new("var1"))),
    ///             ComparisonOp::Eq,
    ///             Box::new(IntegerExpression::Const(0)),
    ///         ),
    ///         BooleanVarConstraint::ComparisonExpression(
    ///             Box::new(IntegerExpression::Atom(Variable::new("var2"))),
    ///             ComparisonOp::Eq,
    ///             Box::new(IntegerExpression::Const(0)),
    ///      )]).unwrap()
    ///     .build();
    /// ```
    pub fn with_initial_variable_constraints(
        self,
        constraints: impl IntoIterator<Item = BooleanVarConstraint>,
    ) -> Result<Self, BuilderError> {
        let mut res = self;
        for constraint in constraints {
            res = res.with_initial_variable_constraint(constraint)?;
        }
        Ok(res)
    }

    /// Check whether the threshold automaton has a specific parameter
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::expressions::*;
    /// use taco_threshold_automaton::general_threshold_automaton::builder::*;
    ///
    /// let builder = GeneralThresholdAutomatonBuilder::new("test_ta1")
    ///     .with_parameter(Parameter::new("n")).unwrap()
    ///     .initialize();
    ///
    /// assert!(builder.has_parameter(&Parameter::new("n")));
    /// ```
    #[inline(always)]
    pub fn has_parameter(&self, param: &Parameter) -> bool {
        self.ta.parameters.contains(param)
    }

    /// Check whether the threshold automaton has a specific variable
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::expressions::*;
    /// use taco_threshold_automaton::general_threshold_automaton::builder::*;
    ///
    /// let builder = GeneralThresholdAutomatonBuilder::new("test_ta1")
    ///     .with_variable(Variable::new("var1")).unwrap()
    ///     .initialize();
    ///
    /// assert!(builder.has_variable(&Variable::new("var1")));
    /// ```
    #[inline(always)]
    pub fn has_variable(&self, var: &Variable) -> bool {
        self.ta.variables.contains(var)
    }

    /// Check whether the threshold automaton has a specific location
    ///
    /// Returns true if the location is present.
    ///
    /// # Example
    ///
    /// ```
    ///
    /// use taco_threshold_automaton::expressions::*;
    /// use taco_threshold_automaton::general_threshold_automaton::builder::*;
    ///
    /// let builder = GeneralThresholdAutomatonBuilder::new("test_ta1")
    ///     .with_location(Location::new("loc1")).unwrap()
    ///     .initialize();
    ///
    /// assert!(builder.has_location(&Location::new("loc1")));
    /// ```
    #[inline(always)]
    pub fn has_location(&self, loc: &Location) -> bool {
        self.ta.locations.contains(loc)
    }

    /// Get an iterator over all locations known to the builder
    ///
    /// # Example
    ///
    /// ```
    ///
    /// use taco_threshold_automaton::expressions::*;
    /// use taco_threshold_automaton::general_threshold_automaton::builder::*;
    ///
    /// let builder = GeneralThresholdAutomatonBuilder::new("test_ta1")
    ///     .with_location(Location::new("loc1")).unwrap()
    ///     .initialize();
    ///
    /// let locations: Vec<&Location> = builder
    ///     .locations()
    ///     .into_iter()
    ///     .collect();
    ///
    /// assert_eq!(locations, vec![&Location::new("loc1")]);
    /// ```
    pub fn locations(&self) -> impl Iterator<Item = &Location> {
        self.ta.locations()
    }

    /// Get an iterator over all variables known to the builder
    ///
    /// # Example
    ///
    /// ```
    ///
    /// use taco_threshold_automaton::expressions::*;
    /// use taco_threshold_automaton::general_threshold_automaton::builder::*;
    ///
    /// let builder = GeneralThresholdAutomatonBuilder::new("test_ta1")
    ///     .with_variable(Variable::new("var1")).unwrap()
    ///     .initialize();
    ///
    /// let variables: Vec<&Variable> = builder
    ///     .variables()
    ///     .into_iter()
    ///     .collect();
    ///
    /// assert_eq!(variables, vec![&Variable::new("var1")]);
    /// ```
    pub fn variables(&self) -> impl Iterator<Item = &Variable> {
        self.ta.variables()
    }

    /// Get an iterator over all parameters known to the builder
    ///
    /// # Example
    ///
    /// ```
    ///
    /// use taco_threshold_automaton::expressions::*;
    /// use taco_threshold_automaton::general_threshold_automaton::builder::*;
    ///
    /// let builder = GeneralThresholdAutomatonBuilder::new("test_ta1")
    ///     .with_parameter(Parameter::new("var1")).unwrap()
    ///     .initialize();
    ///
    /// let parameters: Vec<&Parameter> = builder
    ///     .parameters()
    ///     .into_iter()
    ///     .collect();
    ///
    /// assert_eq!(parameters, vec![&Parameter::new("var1")]);
    /// ```
    pub fn parameters(&self) -> impl Iterator<Item = &Parameter> {
        self.ta.parameters()
    }

    /// Complete the build step and construct the threshold automaton
    #[inline(always)]
    pub fn build(self) -> GeneralThresholdAutomaton {
        self.ta
    }
}

impl IsDeclared<Variable> for InitializedGeneralThresholdAutomatonBuilder {
    fn is_declared(&self, var: &Variable) -> bool {
        self.has_variable(var)
    }
}

impl IsDeclared<Location> for InitializedGeneralThresholdAutomatonBuilder {
    fn is_declared(&self, loc: &Location) -> bool {
        self.has_location(loc)
    }
}

impl IsDeclared<Parameter> for InitializedGeneralThresholdAutomatonBuilder {
    fn is_declared(&self, param: &Parameter) -> bool {
        self.has_parameter(param)
    }
}

/// Builder to construct rules for threshold automata
#[derive(Debug, PartialEq, Eq)]
pub struct RuleBuilder {
    rule: Rule,
}

impl RuleBuilder {
    /// Create a new rule builder
    pub fn new(id: u32, source: Location, target: Location) -> Self {
        RuleBuilder {
            rule: Rule {
                id,
                source,
                target,
                guard: BooleanExpression::True,
                actions: vec![],
            },
        }
    }

    /// Add a guard to the rule
    #[inline(always)]
    pub fn with_guard(mut self, guard: BooleanExpression<Variable>) -> Self {
        self.rule.guard = guard;
        self
    }

    /// Add an action to the rule
    pub fn with_action(mut self, action: Action) -> Self {
        self.rule.actions.push(action);
        self
    }

    /// Add multiple actions to the rule
    pub fn with_actions(mut self, actions: impl IntoIterator<Item = Action>) -> Self {
        for action in actions {
            self.rule.actions.push(action);
        }
        self
    }

    /// Complete the build step and construct the rule
    pub fn build(self) -> Rule {
        self.rule
    }
}

impl Action {
    /// This function counts the number of occurrences of variable `var` in the
    /// expression and checks that no parameters appear
    ///
    /// If a parameter or a variable that is not `var` is found in the
    /// expression, an error is returned
    fn count_number_of_var_occurrences_and_validate(
        var: &Variable,
        update_expr: &IntegerExpression<Variable>,
    ) -> Result<u32, InvalidUpdateError> {
        match update_expr {
            IntegerExpression::Atom(v) => {
                if v != var {
                    return Err(InvalidUpdateError::AdditionalVariable(v.clone()));
                }
                Result::Ok(1)
            }
            IntegerExpression::Const(_) => Result::Ok(0),
            IntegerExpression::Param(p) => Err(InvalidUpdateError::ParameterFound(p.clone())),
            IntegerExpression::BinaryExpr(lhs, _, rhs) => {
                let lhs = Self::count_number_of_var_occurrences_and_validate(var, lhs)?;
                let rhs = Self::count_number_of_var_occurrences_and_validate(var, rhs)?;

                Result::Ok(lhs + rhs)
            }
            IntegerExpression::Neg(expr) => {
                Self::count_number_of_var_occurrences_and_validate(var, expr)
            }
        }
    }

    /// Try to parse a general integer expression into an update expression
    fn parse_to_update_expr(
        var: &Variable,
        update_expr: IntegerExpression<Variable>,
    ) -> Result<UpdateExpression, ActionBuilderError> {
        if let Some(c) = update_expr.try_to_evaluate_to_const() {
            if c != 0 {
                return Err(ActionBuilderError::UpdateExpressionMalformed(
                    var.clone(),
                    update_expr,
                    InvalidUpdateError::ConstantUpdateNonZero(c),
                ));
            }
            return Result::Ok(UpdateExpression::Reset);
        }

        // check for parameters, other variables etc.
        let n_var = Self::count_number_of_var_occurrences_and_validate(var, &update_expr);
        if let Err(err) = n_var {
            return Err(ActionBuilderError::UpdateExpressionMalformed(
                var.clone(),
                update_expr.clone(),
                err,
            ));
        }

        // confirm that var is only referenced once
        if n_var.unwrap() > 1 {
            return Err(ActionBuilderError::UpdateExpressionMalformed(
                var.clone(),
                update_expr.clone(),
                InvalidUpdateError::MultipleOccurrences,
            ));
        }

        // get the overall result of the update (which must now be possible)
        let update = update_expr
            .try_to_evaluate_to_const_with_env(&HashMap::from([(var.clone(), 0)]), &HashMap::new())
            .expect("Failed to evaluate update expression, even though validation passed");

        match update.cmp(&0) {
            Ordering::Equal => Result::Ok(UpdateExpression::Unchanged),
            Ordering::Greater => Result::Ok(UpdateExpression::Inc(update as u32)),
            Ordering::Less => Result::Ok(UpdateExpression::Dec((-update) as u32)),
        }
    }

    /// Create a new reset action which a reset of `var_to_update`.
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::general_threshold_automaton::Action;
    /// use taco_threshold_automaton::expressions::*;
    /// use taco_threshold_automaton::general_threshold_automaton::builder::*;
    ///
    /// // action resetting var1
    /// Action::new_reset(Variable::new("var1"));
    /// ```
    pub fn new_reset(to_update: Variable) -> Self {
        Action {
            variable_to_update: to_update,
            update_expr: UpdateExpression::Reset,
        }
    }

    /// Create a new action that updates variable `var_to_update` with the
    /// result of `update_expr`
    ///
    /// Returns an error if the update expression is malformed, e.g. if the
    /// update refers to a different variable than the one to update.
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::general_threshold_automaton::Action;
    /// use taco_threshold_automaton::expressions::*;
    /// use taco_threshold_automaton::general_threshold_automaton::builder::*;
    ///
    /// // action incrementing var1
    /// Action::new(
    ///     Variable::new("var1"),
    ///     IntegerExpression::Const(1)
    ///         + IntegerExpression::Atom(Variable::new("var1")),
    /// ).unwrap();
    /// ```
    pub fn new(
        to_update: Variable,
        update_expr: IntegerExpression<Variable>,
    ) -> Result<Self, ActionBuilderError> {
        let update_expr = Self::parse_to_update_expr(&to_update, update_expr)?;

        Result::Ok(Action {
            variable_to_update: to_update,
            update_expr,
        })
    }

    /// Create a new action that updates variable `var` according to `update`
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::general_threshold_automaton::Action;
    /// use taco_threshold_automaton::general_threshold_automaton::UpdateExpression;
    /// use taco_threshold_automaton::expressions::Variable;
    /// use taco_threshold_automaton::general_threshold_automaton::builder::*;
    ///
    /// // action incrementing var1
    /// Action::new_with_update(
    ///     Variable::new("var1"),
    ///     UpdateExpression::Inc(1),
    /// );
    /// ```
    pub fn new_with_update(var: Variable, update: UpdateExpression) -> Self {
        Self {
            variable_to_update: var,
            update_expr: update,
        }
    }
}

/// Errors that can occur during the construction of a threshold automaton
#[derive(Debug, Clone)]
pub enum BuilderError {
    /// A parameter with the same name was added multiple times
    DuplicateParameter(Parameter),
    /// A variable with the same name was added multiple times
    DuplicateVariable(Variable),
    /// A location with the same name was added multiple times
    DuplicateLocation(Location),
    /// A rule with the same id was added multiple times
    DuplicateRuleId(Box<Rule>, Box<Rule>),
    /// A rule is malformed
    MalformedRule(Box<Rule>, String),
    /// An action is malformed
    MalformedAction(Box<Action>, String),
    /// A resilience condition is malformed
    MalformedResilienceCondition(Box<ParameterConstraint>, String),
    /// An initial location constraint is malformed
    MalformedInitialLocationConstraint(Box<LocationConstraint>, String),
    /// An initial variable constraint is malformed
    MalformedInitialVariableConstraint(Box<BooleanVarConstraint>, String),
    /// The same name was used multiple times for different components
    NameClash(String),
    /// An unknown component was used in a constraint
    UnknownComponent(String),
}

impl std::error::Error for BuilderError {}

impl std::fmt::Display for BuilderError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BuilderError::DuplicateParameter(param) => {
                write!(f, "Duplicate parameter: {param}")
            }
            BuilderError::DuplicateVariable(var) => write!(f, "Duplicate variable: {var}"),
            BuilderError::DuplicateLocation(loc) => write!(f, "Duplicate location: {loc}"),
            BuilderError::DuplicateRuleId(rule1, rule2) => {
                write!(
                    f,
                    "Duplicate rule id {} appearing in rule {} and {}",
                    rule1.id, rule1, rule2
                )
            }
            BuilderError::MalformedRule(rule, msg) => {
                write!(f, "Malformed rule {}: {} Rule: {}", rule.id, msg, rule)
            }
            BuilderError::UnknownComponent(c) => write!(f, "Unknown component: {c}"),
            BuilderError::MalformedAction(a, msg) => {
                write!(f, "Malformed action: {msg}: {a}")
            }
            BuilderError::MalformedResilienceCondition(rc, msg) => {
                write!(f, "Malformed resilience condition: {msg}: {rc}")
            }
            BuilderError::MalformedInitialLocationConstraint(lc, msg) => {
                write!(f, "Malformed initial location constraint: {msg}: {lc}")
            }
            BuilderError::MalformedInitialVariableConstraint(vc, msg) => {
                write!(f, "Malformed initial variable constraint: {msg}: {vc}")
            }
            BuilderError::NameClash(name) => write!(f, "Name {name} already taken"),
        }
    }
}

/// Custom Error type for a failed construction of an action
#[derive(Debug, Clone)]
pub enum ActionBuilderError {
    /// Error indicating that the supplied update expression was invalid
    UpdateExpressionMalformed(Variable, IntegerExpression<Variable>, InvalidUpdateError),
}

/// Custom Error type to indicate a malformed update expression
#[derive(Debug, Clone)]
pub enum InvalidUpdateError {
    /// Error indicating that the update set the variable to a constant value that is not 0
    ConstantUpdateNonZero(i64),
    /// Error indicating that the update referenced an additional variable
    AdditionalVariable(Variable),
    /// Error indicating that the update referenced a parameter
    ParameterFound(Parameter),
    /// Error indicating that the variable to update occurred multiple times in the update expression
    MultipleOccurrences,
}

impl std::error::Error for ActionBuilderError {}
impl std::error::Error for InvalidUpdateError {}

impl Display for ActionBuilderError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ActionBuilderError::UpdateExpressionMalformed(var, upd_expr, err) => {
                write!(
                    f,
                    "Update expression to variable {var} malformed. Err: {err}; Expression: {upd_expr}"
                )
            }
        }
    }
}

impl From<EvaluationError<Variable>> for InvalidUpdateError {
    fn from(value: EvaluationError<Variable>) -> Self {
        match value {
            EvaluationError::AtomicNotFound(v) => InvalidUpdateError::AdditionalVariable(v),
            EvaluationError::ParameterNotFound(p) => InvalidUpdateError::ParameterFound(p),
        }
    }
}

impl Display for InvalidUpdateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InvalidUpdateError::ConstantUpdateNonZero(c) => write!(
                f,
                "Update expression assigns variable to constant value {c} which is not 0. Such updates are currently unsupported"
            ),
            InvalidUpdateError::AdditionalVariable(var) => write!(
                f,
                "Update expressions references additional variable {var}. Such updates are not allowed in threshold automata."
            ),
            InvalidUpdateError::ParameterFound(p) => write!(
                f,
                "Update expression references parameter {p}. Such updates are not allowed in threshold automata."
            ),
            InvalidUpdateError::MultipleOccurrences => write!(
                f,
                "Update expression references the variable to update more than once. Such expressions are unsupported by threshold automata in general, but might be transformable by hand."
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        BooleanVarConstraint,
        expressions::{BooleanConnective, ComparisonOp},
    };

    use super::*;

    #[test]
    fn test_with_parameter() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");
        let param = Parameter::new("n");

        let ta = builder.with_parameter(param.clone()).unwrap().initialize();

        assert_eq!(
            ta.parameters().collect::<Vec<_>>(),
            vec![&Parameter::new("n")]
        );

        let ta = ta.build();

        assert_eq!(ta.parameters.len(), 1);
        assert!(ta.parameters.contains(&param));
    }

    #[test]
    fn test_with_parameter_duplicate() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");
        let param = Parameter::new("n");

        let error = builder
            .with_parameter(param.clone())
            .unwrap()
            .with_parameter(param.clone());

        assert!(error.is_err());
        assert!(matches!(
            error.clone().unwrap_err(),
            BuilderError::DuplicateParameter(_)
        ));
        assert!(error.unwrap_err().to_string().contains("n"));
    }

    #[test]
    fn test_with_parameters() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");
        let params = HashSet::from([Parameter::new("n"), Parameter::new("m")]);

        let ta = builder
            .with_parameters(params.clone())
            .unwrap()
            .initialize()
            .build();

        assert_eq!(ta.parameters.len(), 2);
        assert_eq!(ta.parameters, params);
    }

    #[test]
    fn test_with_parameter_duplicates_single_add() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");
        let params = vec![Parameter::new("n"), Parameter::new("n")];

        let error = builder.with_parameters(params.clone());

        assert!(error.is_err());
        assert!(matches!(
            error.clone().unwrap_err(),
            BuilderError::DuplicateParameter(_)
        ));
        assert!(error.unwrap_err().to_string().contains("n"))
    }

    #[test]
    fn test_with_parameter_duplicates_separate_add() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");
        let params = vec![Parameter::new("n"), Parameter::new("m")];

        let error = builder
            .with_parameters(params.clone())
            .unwrap()
            .with_parameter(params[1].clone());

        assert!(error.is_err());
        assert!(matches!(
            error.clone().unwrap_err(),
            BuilderError::DuplicateParameter(_)
        ));
        assert!(error.unwrap_err().to_string().contains("m"))
    }

    #[test]
    fn test_with_parameter_name_clash() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");
        let param = Parameter::new("n");

        let error = builder
            .with_variable(Variable::new("n"))
            .unwrap()
            .with_parameter(param.clone());

        assert!(error.is_err());
        assert!(matches!(
            error.clone().unwrap_err(),
            BuilderError::NameClash(_)
        ));
        assert!(error.unwrap_err().to_string().contains("n"))
    }

    #[test]
    fn test_with_location() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");
        let loc = Location::new("A");

        let ta = builder
            .with_location(loc.clone())
            .unwrap()
            .initialize()
            .build();

        assert_eq!(ta.locations.len(), 1);
        assert!(ta.locations.contains(&loc));
    }

    #[test]
    fn test_with_location_duplicate() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");
        let loc = Location::new("A");

        let error = builder
            .with_location(loc.clone())
            .unwrap()
            .with_location(loc.clone());

        assert!(error.is_err());
        assert!(matches!(
            error.clone().unwrap_err(),
            BuilderError::DuplicateLocation(_)
        ));
        assert!(error.unwrap_err().to_string().contains("A"))
    }

    #[test]
    fn test_with_location_name_clash() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");
        let loc = Location::new("n");

        let error = builder
            .with_variable(Variable::new("n"))
            .unwrap()
            .with_location(loc.clone());

        assert!(error.is_err());
        assert!(matches!(
            error.clone().unwrap_err(),
            BuilderError::NameClash(_)
        ));
        assert!(error.unwrap_err().to_string().contains("n"))
    }

    #[test]
    fn test_with_locations() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");
        let locs = HashSet::from([Location::new("A"), Location::new("B")]);

        let ta = builder
            .with_locations(locs.clone())
            .unwrap()
            .initialize()
            .build();

        assert_eq!(ta.locations.len(), 2);
        assert_eq!(ta.locations, locs);
    }

    #[test]
    fn test_with_location_duplicates_single_add() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");
        let locs = vec![Location::new("A"), Location::new("A")];

        let error = builder.with_locations(locs.clone());

        assert!(error.is_err());
        assert!(matches!(
            error.clone().unwrap_err(),
            BuilderError::DuplicateLocation(_)
        ));
        assert!(error.unwrap_err().to_string().contains("A"))
    }

    #[test]
    fn test_with_location_duplicates_separate_add() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");
        let locs = vec![Location::new("A"), Location::new("B")];

        let error = builder
            .with_locations(locs.clone())
            .unwrap()
            .with_location(locs[1].clone());

        assert!(error.is_err());
        assert!(matches!(
            error.clone().unwrap_err(),
            BuilderError::DuplicateLocation(_)
        ));
        assert!(error.unwrap_err().to_string().contains("B"))
    }

    #[test]
    fn test_with_variable() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");
        let var = Variable::new("x");

        let ta = builder
            .with_variable(var.clone())
            .unwrap()
            .initialize()
            .build();

        assert_eq!(ta.variables.len(), 1);
        assert!(ta.variables.contains(&var));
    }

    #[test]
    fn test_with_variable_duplicate() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");
        let var = Variable::new("x");

        let error = builder
            .with_variable(var.clone())
            .unwrap()
            .with_variable(var.clone());

        assert!(error.is_err());
        assert!(matches!(
            error.clone().unwrap_err(),
            BuilderError::DuplicateVariable(_)
        ));
        assert!(error.unwrap_err().to_string().contains("x"))
    }

    #[test]
    fn with_variable_name_clash() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");
        let var = Variable::new("z");

        let error = builder
            .with_parameter(Parameter::new("z"))
            .unwrap()
            .with_variable(var.clone());

        assert!(error.is_err());
        assert!(matches!(
            error.clone().unwrap_err(),
            BuilderError::NameClash(_)
        ));
        assert!(error.unwrap_err().to_string().contains("z"))
    }

    #[test]
    fn test_with_variables() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");
        let vars = HashSet::from([Variable::new("x"), Variable::new("y")]);

        let ta = builder
            .with_variables(vars.clone())
            .unwrap()
            .initialize()
            .build();

        assert_eq!(ta.variables.len(), 2);
        assert_eq!(ta.variables, vars);
    }

    #[test]
    fn test_with_variable_duplicates_single_add() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");
        let vars = vec![Variable::new("x"), Variable::new("x")];

        let error = builder.with_variables(vars.clone());

        assert!(error.is_err());
        assert!(matches!(
            error.clone().unwrap_err(),
            BuilderError::DuplicateVariable(_)
        ));
        assert!(error.unwrap_err().to_string().contains("x"))
    }

    #[test]
    fn test_with_variable_duplicates_separate_add() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");
        let vars = vec![Variable::new("x"), Variable::new("y")];

        let error = builder
            .with_variables(vars.clone())
            .unwrap()
            .with_variable(vars[1].clone());

        assert!(error.is_err());
        assert!(matches!(
            error.clone().unwrap_err(),
            BuilderError::DuplicateVariable(_)
        ));
        assert!(error.unwrap_err().to_string().contains("y"))
    }

    #[test]
    fn test_with_rule() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");

        let rule = Rule {
            id: 0,
            source: Location::new("A"),
            target: Location::new("B"),
            guard: BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ),
            actions: vec![Action {
                variable_to_update: Variable::new("var1"),
                update_expr: UpdateExpression::Reset,
            }],
        };

        let ta = builder
            .with_locations(vec![Location::new("A"), Location::new("B")])
            .unwrap()
            .with_variables(vec![Variable::new("var1")])
            .unwrap()
            .initialize();

        let ta = ta.with_rule(rule.clone()).unwrap().build();

        assert_eq!(ta.outgoing_rules.len(), 1);
        assert_eq!(ta.outgoing_rules.get(&Location::new("A")).unwrap()[0], rule);
    }

    #[test]
    fn test_with_rule_duplicate_rule() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");

        let rule = Rule {
            id: 0,
            source: Location::new("A"),
            target: Location::new("B"),
            guard: BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ),
            actions: vec![Action {
                variable_to_update: Variable::new("var1"),
                update_expr: UpdateExpression::Reset,
            }],
        };

        let ta = builder
            .with_locations(vec![Location::new("A"), Location::new("B")])
            .unwrap()
            .with_variables(vec![Variable::new("var1")])
            .unwrap()
            .initialize();

        let ta = ta.with_rule(rule.clone()).unwrap().with_rule(rule.clone());

        assert!(ta.is_err());
        assert!(matches!(
            ta.unwrap_err(),
            BuilderError::DuplicateRuleId(_, _)
        ));
    }

    #[test]
    fn test_with_rule_double_update() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");

        let rule = Rule {
            id: 0,
            source: Location::new("A"),
            target: Location::new("B"),
            guard: BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ),
            actions: vec![
                Action {
                    variable_to_update: Variable::new("var1"),
                    update_expr: UpdateExpression::Reset,
                },
                Action {
                    variable_to_update: Variable::new("var1"),
                    update_expr: UpdateExpression::Reset,
                },
            ],
        };

        let ta = builder
            .with_locations(vec![Location::new("A"), Location::new("B")])
            .unwrap()
            .with_variables(vec![Variable::new("var1")])
            .unwrap()
            .initialize();

        let ta = ta.with_rule(rule.clone());

        assert!(ta.is_err());
        assert!(matches!(ta.unwrap_err(), BuilderError::MalformedRule(_, _)));
    }

    #[test]
    fn test_with_rule_duplicate_id() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");

        let rule1 = Rule {
            id: 0,
            source: Location::new("A"),
            target: Location::new("B"),
            guard: BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ),
            actions: vec![Action {
                variable_to_update: Variable::new("var1"),
                update_expr: UpdateExpression::Reset,
            }],
        };

        let rule2 = Rule {
            id: 0,
            source: Location::new("B"),
            target: Location::new("A"),
            guard: BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ),
            actions: vec![Action {
                variable_to_update: Variable::new("var1"),
                update_expr: UpdateExpression::Reset,
            }],
        };

        let ta = builder
            .with_locations(vec![Location::new("A"), Location::new("B")])
            .unwrap()
            .with_variables(vec![Variable::new("var1")])
            .unwrap()
            .initialize();

        let ta = ta.with_rule(rule1).unwrap().with_rule(rule2);

        assert!(ta.is_err());
        assert!(matches!(
            ta.clone().unwrap_err(),
            BuilderError::DuplicateRuleId(_, _)
        ));
        assert!(ta.unwrap_err().to_string().contains("0"));
    }

    #[test]
    fn test_with_rule_unknown_guard_var() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");

        let rule = Rule {
            id: 0,
            source: Location::new("A"),
            target: Location::new("B"),
            guard: BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var-uk"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ),
            actions: vec![Action {
                variable_to_update: Variable::new("var1"),
                update_expr: UpdateExpression::Reset,
            }],
        };

        let ta = builder
            .with_locations(vec![Location::new("A"), Location::new("B")])
            .unwrap()
            .with_variables(vec![Variable::new("var1")])
            .unwrap()
            .initialize();

        let ta = ta.with_rule(rule.clone());

        assert!(ta.is_err());
        assert!(matches!(
            ta.clone().unwrap_err(),
            BuilderError::MalformedRule(_, _)
        ));
        assert!(ta.unwrap_err().to_string().contains("var-uk"));
    }

    #[test]
    fn test_with_rule_unknown_guard_param() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");

        let rule = Rule {
            id: 0,
            source: Location::new("A"),
            target: Location::new("B"),
            guard: BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Param(Parameter::new("uk"))),
            ),
            actions: vec![Action {
                variable_to_update: Variable::new("var1"),
                update_expr: UpdateExpression::Reset,
            }],
        };

        let ta = builder
            .with_locations(vec![Location::new("A"), Location::new("B")])
            .unwrap()
            .with_variables(vec![Variable::new("var1")])
            .unwrap()
            .initialize();

        let ta = ta.with_rule(rule.clone());

        assert!(ta.is_err());
        assert!(matches!(
            ta.clone().unwrap_err(),
            BuilderError::MalformedRule(_, _)
        ));
        assert!(ta.unwrap_err().to_string().contains("uk"));
    }

    #[test]
    fn test_with_rule_unknown_action_var() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");

        let rule = Rule {
            id: 0,
            source: Location::new("A"),
            target: Location::new("B"),
            guard: BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ),
            actions: vec![Action {
                variable_to_update: Variable::new("var-uk"),
                update_expr: UpdateExpression::Reset,
            }],
        };

        let ta = builder
            .with_locations(vec![Location::new("A"), Location::new("B")])
            .unwrap()
            .with_variables(vec![Variable::new("var1")])
            .unwrap()
            .initialize();

        let ta = ta.with_rule(rule.clone());

        assert!(ta.is_err());
        assert!(matches!(
            ta.clone().unwrap_err(),
            BuilderError::MalformedRule(_, _)
        ));
        assert!(ta.unwrap_err().to_string().contains("var-uk"));
    }

    #[test]
    fn test_with_rule_unknown_source() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");

        let rule = Rule {
            id: 0,
            source: Location::new("uk"),
            target: Location::new("B"),
            guard: BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ),
            actions: vec![Action {
                variable_to_update: Variable::new("var1"),
                update_expr: UpdateExpression::Reset,
            }],
        };

        let ta = builder
            .with_locations(vec![Location::new("A"), Location::new("B")])
            .unwrap()
            .with_variables(vec![Variable::new("var1")])
            .unwrap()
            .initialize();

        let ta = ta.with_rule(rule.clone());

        assert!(ta.is_err());
        assert!(matches!(
            ta.clone().unwrap_err(),
            BuilderError::MalformedRule(_, _)
        ));
        assert!(ta.unwrap_err().to_string().contains("uk"));
    }

    #[test]
    fn test_with_rule_unknown_target() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");

        let rule = Rule {
            id: 0,
            source: Location::new("A"),
            target: Location::new("uk"),
            guard: BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ),
            actions: vec![Action {
                variable_to_update: Variable::new("var1"),
                update_expr: UpdateExpression::Reset,
            }],
        };

        let ta = builder
            .with_locations(vec![Location::new("A"), Location::new("B")])
            .unwrap()
            .with_variables(vec![Variable::new("var1")])
            .unwrap()
            .initialize();

        let ta = ta.with_rule(rule.clone());

        assert!(ta.is_err());
        assert!(matches!(
            ta.clone().unwrap_err(),
            BuilderError::MalformedRule(_, _)
        ));
    }

    #[test]
    fn test_with_rules() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");

        let rule1 = Rule {
            id: 0,
            source: Location::new("A"),
            target: Location::new("B"),
            guard: BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ),
            actions: vec![Action {
                variable_to_update: Variable::new("var1"),
                update_expr: UpdateExpression::Reset,
            }],
        };

        let rule2 = Rule {
            id: 1,
            source: Location::new("B"),
            target: Location::new("C"),
            guard: BooleanVarConstraint::Not(Box::new(BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(0)),
            ))),
            actions: vec![Action {
                variable_to_update: Variable::new("var2"),
                update_expr: UpdateExpression::Reset,
            }],
        };

        let ta = builder
            .with_locations(vec![
                Location::new("A"),
                Location::new("B"),
                Location::new("C"),
            ])
            .unwrap()
            .with_variables(vec![Variable::new("var1"), Variable::new("var2")])
            .unwrap()
            .initialize();

        let ta = ta
            .with_rules(vec![rule1.clone(), rule2.clone()])
            .unwrap()
            .build();

        assert_eq!(ta.outgoing_rules.len(), 2);
        assert_eq!(
            ta.outgoing_rules.get(&Location::new("A")).unwrap()[0],
            rule1
        );
        assert_eq!(
            ta.outgoing_rules.get(&Location::new("B")).unwrap()[0],
            rule2
        );
    }

    #[test]
    fn test_with_location_constraint() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");

        let loc_constraint = LocationConstraint::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Location::new("A"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(1)),
        );

        let ta = builder
            .with_locations(vec![Location::new("A")])
            .unwrap()
            .initialize()
            .with_initial_location_constraint(loc_constraint.clone())
            .unwrap()
            .build();

        assert_eq!(ta.initial_location_constraint.len(), 1);
        assert_eq!(ta.initial_location_constraint[0], loc_constraint);
    }

    #[test]
    fn test_with_location_constraint_unknown_loc() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");

        let loc_constraint = LocationConstraint::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Location::new("uk"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(1)),
        );

        let ta = builder
            .with_locations(vec![Location::new("A")])
            .unwrap()
            .initialize()
            .with_initial_location_constraint(loc_constraint.clone());

        assert!(ta.is_err());
        assert!(matches!(
            ta.clone().unwrap_err(),
            BuilderError::MalformedInitialLocationConstraint(_, _)
        ));
        assert!(ta.unwrap_err().to_string().contains("uk"));
    }

    #[test]
    fn test_with_variable_constraint() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");

        let var_constraint = BooleanVarConstraint::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Variable::new("A"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Neg(Box::new(IntegerExpression::Const(
                1,
            )))),
        );

        let ta = builder
            .with_variables(vec![Variable::new("A")])
            .unwrap()
            .initialize()
            .with_initial_variable_constraint(var_constraint.clone())
            .unwrap()
            .build();

        assert_eq!(ta.initial_variable_constraint.len(), 1);
        assert_eq!(ta.initial_variable_constraint[0], var_constraint);
    }

    #[test]
    fn test_with_variable_constraint_unknown_var() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");

        let var_constraint = BooleanVarConstraint::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Variable::new("uk"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(1)),
        );

        let ta = builder
            .with_variables(vec![Variable::new("A")])
            .unwrap()
            .initialize()
            .with_initial_variable_constraint(var_constraint.clone());

        assert!(ta.is_err());
        assert!(matches!(
            ta.clone().unwrap_err(),
            BuilderError::MalformedInitialVariableConstraint(_, _)
        ));
        assert!(ta.unwrap_err().to_string().contains("uk"));
    }

    #[test]
    fn test_with_resilience_condition() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");

        let rc = ParameterConstraint::ComparisonExpression(
            Box::new(IntegerExpression::Param(Parameter::new("n"))),
            ComparisonOp::Geq,
            Box::new(IntegerExpression::Const(0)),
        );

        let ta = builder
            .with_parameters(vec![Parameter::new("n")])
            .unwrap()
            .initialize()
            .with_resilience_condition(rc.clone())
            .unwrap()
            .build();

        assert_eq!(ta.resilience_condition.len(), 1);
        assert_eq!(ta.resilience_condition[0], rc);
    }

    #[test]
    fn test_with_resilience_condition_canonicalize1() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");

        let input_rc = ParameterConstraint::ComparisonExpression(
            Box::new(-IntegerExpression::Atom(Parameter::new("n"))),
            ComparisonOp::Geq,
            Box::new(IntegerExpression::Const(0)),
        ) & BooleanExpression::True;

        let expected_rc = ParameterConstraint::ComparisonExpression(
            Box::new(-IntegerExpression::Param(Parameter::new("n"))),
            ComparisonOp::Geq,
            Box::new(IntegerExpression::Const(0)),
        ) & BooleanExpression::True;

        let ta = builder
            .with_parameters(vec![Parameter::new("n")])
            .unwrap()
            .initialize()
            .with_resilience_condition(input_rc)
            .unwrap()
            .build();

        assert_eq!(ta.resilience_condition.len(), 1);
        assert_eq!(ta.resilience_condition[0], expected_rc);
    }

    #[test]
    fn test_with_resilience_condition_canonicalize2() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");

        let input_rc = ParameterConstraint::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Parameter::new("n"))),
            ComparisonOp::Geq,
            Box::new(IntegerExpression::Const(0)),
        ) | ParameterConstraint::ComparisonExpression(
            Box::new(IntegerExpression::Const(0)),
            ComparisonOp::Geq,
            Box::new(IntegerExpression::Atom(Parameter::new("f"))),
        ) & !BooleanExpression::False;

        let expected_rc = ParameterConstraint::ComparisonExpression(
            Box::new(IntegerExpression::Param(Parameter::new("n"))),
            ComparisonOp::Geq,
            Box::new(IntegerExpression::Const(0)),
        ) | ParameterConstraint::ComparisonExpression(
            Box::new(IntegerExpression::Const(0)),
            ComparisonOp::Geq,
            Box::new(IntegerExpression::Param(Parameter::new("f"))),
        ) & !BooleanExpression::False;

        let ta = builder
            .with_parameters(vec![Parameter::new("n"), Parameter::new("f")])
            .unwrap()
            .initialize()
            .with_resilience_condition(input_rc)
            .unwrap()
            .build();

        assert_eq!(ta.resilience_condition.len(), 1);
        assert_eq!(ta.resilience_condition[0], expected_rc);
    }

    #[test]
    fn test_with_resilience_condition_unknown_param() {
        let builder = GeneralThresholdAutomatonBuilder::new("test");

        let rc = ParameterConstraint::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Parameter::new("uk"))),
            ComparisonOp::Geq,
            Box::new(IntegerExpression::Const(0)),
        );

        let ta = builder
            .with_parameters(vec![Parameter::new("n")])
            .unwrap()
            .initialize()
            .with_resilience_condition(rc.clone());

        assert!(ta.is_err());
        assert!(matches!(
            ta.clone().unwrap_err(),
            BuilderError::MalformedResilienceCondition(_, _)
        ));
        assert!(ta.unwrap_err().to_string().contains("uk"));
    }

    #[test]
    fn test_action_new() {
        let action = Action::new(
            Variable::new("x"),
            IntegerExpression::Atom(Variable::new("x")) + IntegerExpression::Const(1),
        )
        .unwrap();

        assert_eq!(action.variable_to_update, Variable::new("x"));
        assert_eq!(action.update_expr, UpdateExpression::Inc(1));

        let action = Action::new(
            Variable::new("x"),
            IntegerExpression::Atom(Variable::new("x")) - IntegerExpression::Const(1),
        )
        .unwrap();

        assert_eq!(action.variable_to_update, Variable::new("x"));
        assert_eq!(action.update_expr, UpdateExpression::Dec(1));

        let action = Action::new(
            Variable::new("x"),
            IntegerExpression::Atom(Variable::new("x")),
        )
        .unwrap();

        assert_eq!(action.variable_to_update, Variable::new("x"));
        assert_eq!(action.update_expr, UpdateExpression::Unchanged);
    }

    #[test]
    fn test_canonicalize_reset_in_action() {
        let action = Action::new(Variable::new("x"), IntegerExpression::Const(0)).unwrap();

        assert_eq!(action.variable_to_update, Variable::new("x"));
        assert_eq!(action.update_expr, UpdateExpression::Reset);
    }

    #[test]
    fn test_action_const_update_non_zero() {
        let action = Action::new(Variable::new("x"), IntegerExpression::Const(1));

        assert!(action.is_err());
        assert!(matches!(
            action.clone().unwrap_err(),
            ActionBuilderError::UpdateExpressionMalformed(
                _,
                _,
                InvalidUpdateError::ConstantUpdateNonZero(1)
            )
        ));
        assert!(action.unwrap_err().to_string().contains(&1.to_string()));
    }

    #[test]
    fn test_action_new_with_different_var() {
        let action = Action::new(
            Variable::new("x"),
            IntegerExpression::Atom(Variable::new("y")) + IntegerExpression::Const(1),
        );

        assert!(action.is_err());
        assert!(matches!(
            action.clone().unwrap_err(),
            ActionBuilderError::UpdateExpressionMalformed(
                _,
                _,
                InvalidUpdateError::AdditionalVariable(_)
            )
        ));
        assert!(
            action
                .unwrap_err()
                .to_string()
                .contains(&Variable::new("y").to_string())
        );
    }

    #[test]
    fn action_new_with_parameter() {
        let action = Action::new(
            Variable::new("x"),
            IntegerExpression::Param(Parameter::new("n")) + IntegerExpression::Const(1),
        );

        assert!(action.is_err());
        assert!(matches!(
            action.clone().unwrap_err(),
            ActionBuilderError::UpdateExpressionMalformed(
                _,
                _,
                InvalidUpdateError::ParameterFound(_)
            )
        ));
        assert!(
            action
                .unwrap_err()
                .to_string()
                .contains(&Parameter::new("n").to_string())
        );
    }

    #[test]
    fn action_new_multiple_var() {
        let action = Action::new(
            Variable::new("x"),
            IntegerExpression::Atom(Variable::new("x"))
                * IntegerExpression::Atom(Variable::new("x"))
                + IntegerExpression::Const(1),
        );

        assert!(action.is_err());
        assert!(matches!(
            action.clone().unwrap_err(),
            ActionBuilderError::UpdateExpressionMalformed(
                _,
                _,
                InvalidUpdateError::MultipleOccurrences
            )
        ));
        assert!(
            action
                .unwrap_err()
                .to_string()
                .contains(&Variable::new("x").to_string())
        );
    }

    #[test]
    fn test_complete_automaton() {
        let expected_ta = GeneralThresholdAutomaton {
            name: "test_ta1".to_string(),
            parameters: HashSet::from([
                Parameter::new("n"),
                Parameter::new("t"),
                Parameter::new("f"),
            ]),
            variables: HashSet::from([
                Variable::new("var1"),
                Variable::new("var2"),
                Variable::new("var3"),
            ]),
            locations: HashSet::from([
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
            ]),
            initial_variable_constraint: vec![],
            outgoing_rules: HashMap::from([
                (
                    Location::new("loc1"),
                    vec![Rule {
                        id: 0,
                        source: Location::new("loc1"),
                        target: Location::new("loc2"),
                        guard: BooleanExpression::True,
                        actions: vec![],
                    }],
                ),
                (
                    Location::new("loc2"),
                    vec![Rule {
                        id: 1,
                        source: Location::new("loc2"),
                        target: Location::new("loc3"),
                        guard: BooleanExpression::BinaryExpression(
                            Box::new(BooleanVarConstraint::ComparisonExpression(
                                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                                ComparisonOp::Eq,
                                Box::new(IntegerExpression::Const(1)),
                            )),
                            BooleanConnective::And,
                            Box::new(BooleanVarConstraint::ComparisonExpression(
                                Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                                ComparisonOp::Eq,
                                Box::new(IntegerExpression::Param(Parameter::new("n"))),
                            )),
                        ),
                        actions: vec![
                            Action {
                                variable_to_update: Variable::new("var3"),
                                update_expr: UpdateExpression::Reset,
                            },
                            Action {
                                variable_to_update: Variable::new("var1"),
                                update_expr: UpdateExpression::Inc(1),
                            },
                        ],
                    }],
                ),
            ]),

            initial_location_constraint: vec![LocationConstraint::BinaryExpression(
                Box::new(LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                    ComparisonOp::Eq,
                    Box::new(
                        IntegerExpression::Param(Parameter::new("n"))
                            - IntegerExpression::Param(Parameter::new("f")),
                    ),
                )),
                BooleanConnective::Or,
                Box::new(LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )),
            )],

            resilience_condition: vec![ParameterConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Param(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(
                    IntegerExpression::Const(3) * IntegerExpression::Param(Parameter::new("f")),
                ),
            )],
        };

        let ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
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
            .with_rules(vec![
                RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2")).build(),
                RuleBuilder::new(1, Location::new("loc2"), Location::new("loc3"))
                    .with_guard(
                        BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Const(1)),
                        ) & BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Param(Parameter::new("n"))),
                        ),
                    )
                    .with_action(Action::new_reset(Variable::new("var3")))
                    .with_action(
                        Action::new(
                            Variable::new("var1"),
                            IntegerExpression::Atom(Variable::new("var1"))
                                + IntegerExpression::Const(1),
                        )
                        .unwrap(),
                    )
                    .build(),
            ])
            .unwrap()
            .with_initial_location_constraint(
                LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                    ComparisonOp::Eq,
                    Box::new(
                        IntegerExpression::Param(Parameter::new("n"))
                            - IntegerExpression::Param(Parameter::new("f")),
                    ),
                ) | LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            )
            .unwrap()
            .with_resilience_condition(ParameterConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(
                    IntegerExpression::Const(3) * IntegerExpression::Atom(Parameter::new("f")),
                ),
            ))
            .unwrap()
            .build();

        assert_eq!(ta, expected_ta)
    }

    #[test]
    fn test_from_evaluation_error_to_update_err() {
        let error = EvaluationError::AtomicNotFound(Variable::new("x"));
        let update_err = InvalidUpdateError::from(error);
        assert!(matches!(
            update_err,
            InvalidUpdateError::AdditionalVariable(_)
        ));

        let error = EvaluationError::ParameterNotFound(Parameter::new("n"));
        let update_err = InvalidUpdateError::from(error);
        assert!(matches!(update_err, InvalidUpdateError::ParameterFound(_)));
    }
}
