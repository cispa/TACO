//! Implementation of functionality for [`LIAThresholdAutomaton`], [`LIARule`]
//! and the guard types
//!
//! This module contains the structs and traits for the linear integer arithmetic
//! threshold automaton representation.

use std::collections::HashSet;

use std::error::Error;
use std::fmt::Display;

use taco_display_utils::{
    display_iterator_stable_order, indent_all, join_iterator, join_iterator_and_add_back,
};

use crate::expressions::fraction::Fraction;
use crate::expressions::{
    And, Atomic, BooleanConnective, BooleanExpression, IntegerExpression, Or, Parameter, Variable,
};
use crate::expressions::{IsDeclared, Location};
use crate::general_threshold_automaton::{Action, GeneralThresholdAutomaton, Rule};
use crate::lia_threshold_automaton::integer_thresholds::{
    IntoNoDivBooleanExpr, Threshold, ThresholdConstraint, ThresholdConstraintOver, WeightedSum,
};
use crate::{
    LocationConstraint, RuleDefinition, ThresholdAutomaton, VariableConstraint, impl_bitand,
    impl_bitor,
};

use super::{
    ComparisonConstraint, ComparisonConstraintCreationError, LIARule, LIAThresholdAutomaton,
    LIATransformationError, LIAVariableConstraint, SingleAtomConstraint, SumAtomConstraint,
    SumVarConstraintCreationError,
};

impl LIAThresholdAutomaton {
    /// Get the maximum number of thresholds in a single rule of the threshold
    /// automaton
    pub fn get_max_number_of_thresholds_per_rule(&self) -> u32 {
        self.rules
            .values()
            .flatten()
            .map(|rule| rule.number_of_thresholds())
            .max()
            .unwrap_or(0)
    }

    /// Get a reference to the [`GeneralThresholdAutomaton`] this automaton has
    /// been derived from
    pub fn get_ta(&self) -> &GeneralThresholdAutomaton {
        &self.ta
    }

    /// Check if the canonical threshold automaton contains a guard over as sum
    /// of variables, i.e., some guard contains a [`SumAtomConstraint`]
    pub fn has_sum_var_threshold_guard(&self) -> bool {
        self.rules
            .values()
            .flatten()
            .any(|r| r.guard().has_sum_var())
    }

    /// Check if the canonical threshold automaton has a comparison guard,i.e.,
    /// some guard contains a [`ComparisonConstraint`]
    pub fn has_comparison_guard(&self) -> bool {
        self.rules
            .values()
            .flatten()
            .any(|r| r.guard().has_comparison_guard())
    }

    /// Get all appearing [`SingleAtomConstraint`]s
    ///
    /// This function returns all appearing [`SingleAtomConstraint`]s in the
    /// rules of a threshold automaton. The constraints are deduplicated.
    pub fn get_single_var_constraints_rules(&self) -> HashSet<SingleAtomConstraint<Variable>> {
        self.rules()
            .flat_map(|r| r.guard().get_single_var_constraints())
            .collect()
    }

    /// Get all appearing [`SumAtomConstraint`]s
    ///
    /// This function returns all appearing [`SumAtomConstraint`]s in the
    /// rules of a threshold automaton. The constraints are deduplicated.
    pub fn get_sum_var_constraints(&self) -> HashSet<SumAtomConstraint<Variable>> {
        self.rules()
            .flat_map(|r| r.guard().get_multi_variable_guards())
            .collect()
    }

    /// Get all appearing [`ComparisonConstraint`]s
    ///
    /// This function returns all appearing [`ComparisonConstraint`]s in the
    ///rules of a threshold automaton. The constraints are deduplicated.
    pub fn get_comparison_guards(&self) -> HashSet<ComparisonConstraint<Variable>> {
        self.rules()
            .flat_map(|r| r.guard().get_comparison_guards())
            .collect()
    }

    /// Get the number of distinct thresholds appearing in the definition of the
    /// threshold automaton
    pub fn get_thresholds(&self) -> HashSet<Threshold> {
        self.rules()
            .flat_map(|r| r.get_distinct_thresholds())
            .collect()
    }

    /// Get the [`Rule`] this rule has been derived from
    pub fn get_derived_rule(&self, r: &LIARule) -> Rule {
        self.ta
            .rules()
            .find(|rule| {
                rule.id() == r.id() && rule.source() == r.source() && rule.target() == r.target()
            })
            .expect("Could not find derived rule")
            .clone()
    }
}

impl ThresholdAutomaton for LIAThresholdAutomaton {
    type Rule = LIARule;
    type InitialVariableConstraintType = LIAVariableConstraint;

    fn name(&self) -> &str {
        self.ta.name()
    }

    fn variables(&self) -> impl Iterator<Item = &Variable> {
        // TODO: remove as soon as proper ordering is implemented
        self.ta
            .variables()
            .chain(self.additional_vars_for_sums.keys())
    }

    fn parameters(&self) -> impl Iterator<Item = &Parameter> {
        self.ta.parameters()
    }

    fn locations(&self) -> impl Iterator<Item = &Location> {
        self.ta.locations()
    }

    fn resilience_conditions(
        &self,
    ) -> impl Iterator<Item = &crate::expressions::BooleanExpression<Parameter>> {
        self.ta.resilience_conditions()
    }

    fn can_be_initial_location(&self, location: &Location) -> bool {
        self.ta.can_be_initial_location(location)
    }

    fn rules(&self) -> impl Iterator<Item = &Self::Rule> {
        self.rules.values().flatten()
    }

    fn incoming_rules(&self, location: &Location) -> impl Iterator<Item = &Self::Rule> {
        self.rules().filter(move |r| r.target() == location)
    }

    fn outgoing_rules(&self, location: &Location) -> impl Iterator<Item = &Self::Rule> {
        self.rules.get(location).into_iter().flatten()
    }

    fn initial_location_constraints(&self) -> impl Iterator<Item = &LocationConstraint> {
        self.ta.initial_location_conditions()
    }

    fn initial_variable_constraints(&self) -> impl Iterator<Item = &LIAVariableConstraint> {
        self.init_variable_constr.iter()
    }
}

// Here we decided to use the bymc format to display a threshold automaton,
// since it is well documented and easy to read.
impl Display for LIAThresholdAutomaton {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let variables = format!(
            "shared {};",
            display_iterator_stable_order(self.ta.variables())
        );
        let parameters = format!(
            "parameters {};",
            display_iterator_stable_order(self.ta.parameters())
        );

        let rc = format!(
            "assumptions ({}) {{\n{}}}",
            self.ta.resilience_conditions().count(),
            indent_all(join_iterator_and_add_back(
                self.ta.resilience_conditions(),
                ";\n"
            ))
        );

        let mut loc_str = String::new();
        let mut locations = self.ta.locations().collect::<Vec<_>>();
        locations.sort();
        for (i, loc) in locations.into_iter().enumerate() {
            loc_str += &format!("{loc}:[{i}];\n");
        }
        let locations = format!(
            "locations ({}) {{\n{}}}",
            self.ta.locations().count(),
            indent_all(loc_str)
        );

        let initial_cond = format!(
            "inits ({}) {{\n{}}}",
            self.ta.initial_location_conditions().count() + self.init_variable_constr.len(),
            indent_all(
                join_iterator_and_add_back(self.ta.initial_location_conditions(), ";\n")
                    + &join_iterator_and_add_back(
                        self.init_variable_constr
                            .iter()
                            .map(|cstr| cstr.as_boolean_expr()),
                        ";\n"
                    )
            )
        );

        let mut sorted_rules_by_id = self.rules.values().flatten().collect::<Vec<_>>();
        sorted_rules_by_id.sort_by_key(|r| &r.id);
        let rules = format!(
            "rules ({}) {{\n{}}}",
            self.rules.len(),
            indent_all(join_iterator_and_add_back(
                sorted_rules_by_id.into_iter(),
                ";\n"
            ))
        );

        let ta_body = format!(
            "{variables}\n\n{parameters}\n\n{rc}\n\n{locations}\n\n{initial_cond}\n\n{rules}"
        );

        write!(
            f,
            "thresholdAutomaton {} {{\n{}\n}}\n",
            self.ta.name(),
            indent_all(ta_body)
        )
    }
}

impl IsDeclared<Parameter> for LIAThresholdAutomaton {
    fn is_declared(&self, obj: &Parameter) -> bool {
        self.ta.is_declared(obj)
    }
}

impl IsDeclared<Variable> for LIAThresholdAutomaton {
    fn is_declared(&self, obj: &Variable) -> bool {
        self.ta.is_declared(obj)
    }
}

impl IsDeclared<Location> for LIAThresholdAutomaton {
    fn is_declared(&self, obj: &Location) -> bool {
        self.ta.is_declared(obj)
    }
}

impl LIARule {
    /// Get all distinct thresholds appearing in the guard of the rule
    fn get_distinct_thresholds(&self) -> HashSet<Threshold> {
        self.guard.get_distinct_thresholds()
    }

    /// Get the number of thresholds appearing in the guard
    pub fn number_of_thresholds(&self) -> u32 {
        self.guard.count_number_of_thresholds()
    }

    /// Returns the number of updates in the rule
    pub fn number_of_updates(&self) -> u32 {
        self.actions.len() as u32
    }
}

impl RuleDefinition for LIARule {
    type Action = Action;

    type Guard = LIAVariableConstraint;

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

impl Display for LIARule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let guard_string = self.guard.to_string();
        let update_string = join_iterator(self.actions.iter(), "; ");

        let rule_body = indent_all(format!("when ( {guard_string} )\ndo {{ {update_string} }}"));

        write!(
            f,
            "{}: {} -> {}\n{}",
            self.id, self.source, self.target, rule_body
        )
    }
}

impl LIAVariableConstraint {
    /// Check whether constraint is constant true
    ///
    /// This function checks whether the constraint corresponds to `true`. It
    /// will not do semantic analysis, i.e. a constraint of the form `0 = 0`
    /// will not be considered as top.
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::lia_threshold_automaton::LIAVariableConstraint;
    ///
    /// assert!(LIAVariableConstraint::True.is_top());
    /// assert!(!LIAVariableConstraint::False.is_top());
    /// ```
    pub fn is_top(&self) -> bool {
        match self {
            LIAVariableConstraint::False
            | LIAVariableConstraint::ComparisonConstraint(_)
            | LIAVariableConstraint::SingleVarConstraint(_)
            | LIAVariableConstraint::SumVarConstraint(_) => false,
            LIAVariableConstraint::BinaryGuard(lhs, BooleanConnective::And, rhs) => {
                lhs.is_top() && rhs.is_top()
            }
            LIAVariableConstraint::BinaryGuard(lhs, BooleanConnective::Or, rhs) => {
                lhs.is_top() || rhs.is_top()
            }
            LIAVariableConstraint::True => true,
        }
    }

    /// Check whether constraint is constant false
    ///
    /// This function checks whether the constraint corresponds to `false`. It
    /// will not do semantic analysis, i.e. a constraint of the form `0 = 1`
    /// will not be considered as bottom.
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::lia_threshold_automaton::LIAVariableConstraint;
    ///
    /// assert!(LIAVariableConstraint::False.is_bot());
    /// assert!(!LIAVariableConstraint::True.is_bot());
    /// ```
    pub fn is_bot(&self) -> bool {
        match self {
            LIAVariableConstraint::True
            | LIAVariableConstraint::ComparisonConstraint(_)
            | LIAVariableConstraint::SingleVarConstraint(_)
            | LIAVariableConstraint::SumVarConstraint(_) => false,
            LIAVariableConstraint::BinaryGuard(lhs, BooleanConnective::And, rhs) => {
                lhs.is_bot() || rhs.is_bot()
            }
            LIAVariableConstraint::BinaryGuard(lhs, BooleanConnective::Or, rhs) => {
                lhs.is_bot() && rhs.is_bot()
            }
            LIAVariableConstraint::False => true,
        }
    }

    /// Get all [`Threshold`]s appearing in the constraint
    fn get_distinct_thresholds(&self) -> HashSet<Threshold> {
        match self {
            LIAVariableConstraint::ComparisonConstraint(cg) => {
                HashSet::from([cg.get_threshold().clone()])
            }
            LIAVariableConstraint::SingleVarConstraint(svg) => {
                HashSet::from([svg.get_threshold().clone()])
            }
            LIAVariableConstraint::SumVarConstraint(mvg) => {
                HashSet::from([mvg.get_threshold().clone()])
            }
            LIAVariableConstraint::BinaryGuard(lhs, _, rhs) => {
                let mut l_thr = lhs.get_distinct_thresholds();
                let r_thr = rhs.get_distinct_thresholds();
                l_thr.extend(r_thr);
                l_thr
            }
            LIAVariableConstraint::True | LIAVariableConstraint::False => HashSet::new(),
        }
    }

    /// Count the number of thresholds appearing in the constraint
    pub fn count_number_of_thresholds(&self) -> u32 {
        match self {
            LIAVariableConstraint::ComparisonConstraint(_)
            | LIAVariableConstraint::SingleVarConstraint(_)
            | LIAVariableConstraint::SumVarConstraint(_) => 1,
            LIAVariableConstraint::BinaryGuard(lhs, _, rhs) => {
                lhs.count_number_of_thresholds() + rhs.count_number_of_thresholds()
            }
            LIAVariableConstraint::True => 0,
            LIAVariableConstraint::False => 0,
        }
    }

    /// Check if the guard contains a [`SumAtomConstraint`] in its constraint
    pub fn has_sum_var(&self) -> bool {
        match self {
            LIAVariableConstraint::SumVarConstraint(_) => true,
            LIAVariableConstraint::BinaryGuard(lhs, _, rhs) => {
                lhs.has_sum_var() || rhs.has_sum_var()
            }
            _ => false,
        }
    }

    /// Check if the guard contains a  [`ComparisonConstraint`] in its
    /// constraint
    pub fn has_comparison_guard(&self) -> bool {
        match self {
            LIAVariableConstraint::ComparisonConstraint(_) => true,
            LIAVariableConstraint::BinaryGuard(lhs, _, rhs) => {
                lhs.has_comparison_guard() || rhs.has_comparison_guard()
            }
            _ => false,
        }
    }

    /// Get all [`SingleAtomConstraint`]s appearing in the constraint
    pub fn get_single_var_constraints(&self) -> Vec<SingleAtomConstraint<Variable>> {
        match self {
            LIAVariableConstraint::SingleVarConstraint(s) => vec![s.clone()],
            LIAVariableConstraint::BinaryGuard(lhs, _, rhs) => {
                let mut guards = lhs.get_single_var_constraints();
                guards.extend(rhs.get_single_var_constraints());
                guards
            }
            LIAVariableConstraint::SumVarConstraint(_)
            | LIAVariableConstraint::ComparisonConstraint(_)
            | LIAVariableConstraint::True
            | LIAVariableConstraint::False => vec![],
        }
    }

    /// Get all [`SumAtomConstraint`] appearing in the constraint
    pub fn get_multi_variable_guards(&self) -> Vec<SumAtomConstraint<Variable>> {
        match self {
            LIAVariableConstraint::SumVarConstraint(m) => vec![m.clone()],
            LIAVariableConstraint::BinaryGuard(lhs, _, rhs) => {
                let mut guards = lhs.get_multi_variable_guards();
                guards.extend(rhs.get_multi_variable_guards());
                guards
            }
            LIAVariableConstraint::SingleVarConstraint(_)
            | LIAVariableConstraint::ComparisonConstraint(_)
            | LIAVariableConstraint::True
            | LIAVariableConstraint::False => vec![],
        }
    }

    /// Get all [`ComparisonConstraint`] appearing in the constraint
    pub fn get_comparison_guards(&self) -> Vec<ComparisonConstraint<Variable>> {
        match self {
            LIAVariableConstraint::ComparisonConstraint(c) => vec![c.clone()],
            LIAVariableConstraint::BinaryGuard(lhs, _, rhs) => {
                let mut guards = lhs.get_comparison_guards();
                guards.extend(rhs.get_comparison_guards());
                guards
            }
            LIAVariableConstraint::SingleVarConstraint(_)
            | LIAVariableConstraint::SumVarConstraint(_)
            | LIAVariableConstraint::True
            | LIAVariableConstraint::False => vec![],
        }
    }

    /// Check if the constraint is an upper guard
    pub fn is_upper_guard(&self) -> bool {
        match self {
            LIAVariableConstraint::ComparisonConstraint(c) => c.is_upper_guard(),
            LIAVariableConstraint::SingleVarConstraint(s) => s.is_upper_guard(),
            LIAVariableConstraint::SumVarConstraint(m) => m.is_upper_guard(),
            LIAVariableConstraint::BinaryGuard(lhs, _, rhs) => {
                lhs.is_upper_guard() || rhs.is_upper_guard()
            }
            LIAVariableConstraint::True | LIAVariableConstraint::False => false,
        }
    }

    /// Check if the constraint is a lower guard
    pub fn is_lower_guard(&self) -> bool {
        match self {
            LIAVariableConstraint::ComparisonConstraint(c) => c.is_lower_guard(),
            LIAVariableConstraint::SingleVarConstraint(s) => s.is_lower_guard(),
            LIAVariableConstraint::SumVarConstraint(m) => m.is_lower_guard(),
            LIAVariableConstraint::BinaryGuard(lhs, _, rhs) => {
                lhs.is_lower_guard() || rhs.is_lower_guard()
            }
            LIAVariableConstraint::True | LIAVariableConstraint::False => false,
        }
    }
}

impl And for LIAVariableConstraint {
    fn and(self, other: Self) -> Self {
        LIAVariableConstraint::BinaryGuard(Box::new(self), BooleanConnective::And, Box::new(other))
    }
}
impl_bitand!(LIAVariableConstraint);

impl Or for LIAVariableConstraint {
    fn or(self, other: Self) -> Self {
        LIAVariableConstraint::BinaryGuard(Box::new(self), BooleanConnective::Or, Box::new(other))
    }
}
impl_bitor!(LIAVariableConstraint);

impl VariableConstraint for LIAVariableConstraint {
    fn as_boolean_expr(&self) -> crate::expressions::BooleanExpression<Variable> {
        match self {
            LIAVariableConstraint::ComparisonConstraint(guard) => guard.to_boolean_expr(),
            LIAVariableConstraint::SingleVarConstraint(guard) => guard.to_boolean_expr(),
            LIAVariableConstraint::SumVarConstraint(guard) => guard.to_boolean_expr(),
            LIAVariableConstraint::BinaryGuard(lhs, boolean_connective, rhs) => {
                let lhs = lhs.as_boolean_expr();
                let rhs = rhs.as_boolean_expr();
                BooleanExpression::BinaryExpression(
                    Box::new(lhs),
                    *boolean_connective,
                    Box::new(rhs),
                )
            }
            LIAVariableConstraint::True => BooleanExpression::True,
            LIAVariableConstraint::False => BooleanExpression::False,
        }
    }
}

impl<T: Atomic> SingleAtomConstraint<T> {
    /// Create a new single variable constraint
    pub fn new(atom: T, thr: ThresholdConstraint) -> Self {
        Self(ThresholdConstraintOver::new(atom, thr))
    }

    /// Check if the constraint is an upper guard
    pub fn is_upper_guard(&self) -> bool {
        self.0.is_upper_guard()
    }

    /// Check if the guard is a lower guard
    pub fn is_lower_guard(&self) -> bool {
        self.0.is_lower_guard()
    }

    /// Get the variable the constraint constrains
    pub fn get_atom(&self) -> &T {
        self.0.get_t()
    }

    /// Transform the constraint into a [`BooleanExpression`]
    pub fn to_boolean_expr<S>(&self) -> BooleanExpression<S>
    where
        T: IntoNoDivBooleanExpr<S>,
        IntegerExpression<S>: From<T>,
        S: Atomic,
    {
        self.0.encode_to_boolean_expr()
    }

    /// Get the threshold of the guard
    pub fn get_threshold(&self) -> &Threshold {
        self.0.get_threshold()
    }

    /// Get the threshold constraint of the guard
    pub fn get_threshold_constraint(&self) -> &ThresholdConstraint {
        self.0.get_threshold_constraint()
    }
}

impl<T: Atomic> Display for SingleAtomConstraint<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<T: Atomic> SumAtomConstraint<T> {
    /// Try to create a new [`SumAtomConstraint`]
    ///
    /// A [`SumAtomConstraint`] constraints a (weighted) sum of **multiple**
    /// variables, where all variable weights are positive (or all negative, in
    /// this case the constraint is transformed such that all variable are
    /// positive). Any other form would result in a [`ComparisonConstraint`] or
    /// if there is only a single variable a [`SingleAtomConstraint`].
    ///
    /// Returns an [`SumVarConstraintCreationError`] if the coefficients are
    /// mixed or only a single variable is present.
    pub fn try_new<F: Into<Fraction>, I: IntoIterator<Item = (T, F)> + Clone>(
        atoms: I,
        mut thr: ThresholdConstraint,
    ) -> Result<Self, SumVarConstraintCreationError> {
        let mut variables = WeightedSum::new(atoms);

        if (&variables).into_iter().count() == 1 {
            return Err(SumVarConstraintCreationError::IsSingleAtomConstraint);
        }

        if (&variables).into_iter().any(|(_, f)| f.is_negative())
            && (&variables).into_iter().any(|(_, f)| !f.is_negative())
        {
            return Err(SumVarConstraintCreationError::IsComparisonConstraint);
        }

        if (&variables).into_iter().all(|(_, f)| f.is_negative()) {
            variables.scale(-Fraction::from(1));
            thr.scale(-Fraction::from(1));
        }

        let constr = ThresholdConstraintOver::new(variables, thr);

        Ok(Self(constr))
    }

    /// Check if the guard is an upper guard
    pub fn is_upper_guard(&self) -> bool {
        self.0.is_upper_guard()
    }

    /// Check if the guard is a lower guard
    pub fn is_lower_guard(&self) -> bool {
        self.0.is_lower_guard()
    }

    /// Get the variable
    pub fn get_atoms(&self) -> &WeightedSum<T> {
        self.0.get_t()
    }

    /// Get boolean expression of the guard
    pub fn to_boolean_expr<S>(&self) -> BooleanExpression<S>
    where
        T: IntoNoDivBooleanExpr<S>,
        IntegerExpression<S>: From<T>,
        S: Atomic,
    {
        self.0.encode_to_boolean_expr()
    }

    /// Get the threshold of the guard
    pub fn get_threshold(&self) -> &Threshold {
        self.0.get_threshold()
    }

    /// Get the threshold constraint of the guard
    pub fn get_threshold_constraint(&self) -> &ThresholdConstraint {
        self.0.get_threshold_constraint()
    }
}

impl<T: Atomic> Display for SumAtomConstraint<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Error for SumVarConstraintCreationError {}

impl Display for SumVarConstraintCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SumVarConstraintCreationError::IsComparisonConstraint => {
                write!(f, "Guard is a ComparisonGuard not a MultiVarThresholdGuard")
            }
            SumVarConstraintCreationError::IsSingleAtomConstraint => {
                write!(
                    f,
                    "Guard is a SingleVarThresholdGuard not a MultiVarThresholdGuard"
                )
            }
        }
    }
}

impl<T: Atomic> ComparisonConstraint<T> {
    /// Create a [`ComparisonConstraint`]
    ///
    /// A comparison constraint constrains a weighted sum over **multiple**
    /// variables where at least one has a negative and at least one has a
    /// positive coefficient.
    /// In any other case the guard would be a [`SingleAtomConstraint`] or a
    /// [`SumAtomConstraint`]. In this case a
    /// [`ComparisonConstraintCreationError`] is returned.
    pub fn try_new<I: IntoIterator<Item = (T, Fraction)> + Clone>(
        atoms: I,
        thr: ThresholdConstraint,
    ) -> Result<Self, ComparisonConstraintCreationError> {
        if atoms.clone().into_iter().all(|(_, f)| f.is_negative())
            || atoms.clone().into_iter().all(|(_, f)| !f.is_negative())
        {
            return Err(ComparisonConstraintCreationError::IsSumVarConstraint);
        }

        let atoms = WeightedSum::new(atoms);
        let symbolic_constraint = ThresholdConstraintOver::new(atoms, thr);

        Ok(Self(symbolic_constraint))
    }

    /// Check if the guard is an upper guard
    pub fn is_upper_guard(&self) -> bool {
        self.0.is_upper_guard()
    }

    /// Check if the guard is a lower guard
    pub fn is_lower_guard(&self) -> bool {
        self.0.is_lower_guard()
    }

    /// Get the boolean expression representing the threshold
    pub fn to_boolean_expr<S>(&self) -> BooleanExpression<S>
    where
        T: IntoNoDivBooleanExpr<S>,
        IntegerExpression<S>: From<T>,
        S: Atomic,
    {
        self.0.encode_to_boolean_expr()
    }

    /// Get the threshold of the constraint
    pub fn get_threshold(&self) -> &Threshold {
        self.0.get_threshold()
    }

    /// Get the threshold constraint of the constraint
    pub fn get_threshold_constraint(&self) -> &ThresholdConstraint {
        self.0.get_threshold_constraint()
    }
}

impl<T: Atomic> Display for ComparisonConstraint<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)?;

        Ok(())
    }
}

impl Error for ComparisonConstraintCreationError {}

impl Display for ComparisonConstraintCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ComparisonConstraintCreationError::IsSumVarConstraint => {
                write!(f, "Guard is a MultiVarThresholdGuard not a ComparisonGuard")
            }
        }
    }
}

impl Display for LIAVariableConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LIAVariableConstraint::SumVarConstraint(g) => write!(f, "{g}"),
            LIAVariableConstraint::BinaryGuard(lhs, op, rhs) => {
                write!(f, "({lhs}) {op} ({rhs})")
            }
            LIAVariableConstraint::True => write!(f, "true"),
            LIAVariableConstraint::False => write!(f, "false"),
            LIAVariableConstraint::ComparisonConstraint(g) => write!(f, "{g}"),
            LIAVariableConstraint::SingleVarConstraint(g) => write!(f, "{g}"),
        }
    }
}

impl Error for LIATransformationError {}

impl Display for LIATransformationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LIATransformationError::GuardError(rule, guard, err) => write!(
                f,
                "Error while transforming guard {guard} of rule {rule}: {err}"
            ),
            LIATransformationError::InitialConstraintError(
                boolean_expression,
                guard_rewrite_error,
            ) => {
                write!(
                    f,
                    "Error while transforming initial constraint {boolean_expression} into linear arithmetic: {guard_rewrite_error}"
                )
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{
        collections::{BTreeMap, HashMap, HashSet},
        vec,
    };

    use crate::{
        BooleanVarConstraint, LocationConstraint, ParameterConstraint, RuleDefinition,
        ThresholdAutomaton, VariableConstraint,
        expressions::{
            BooleanConnective, BooleanExpression, ComparisonOp, IntegerExpression, IntegerOp,
            Location, Parameter, Variable, fraction::Fraction,
        },
        general_threshold_automaton::{
            Action,
            builder::{GeneralThresholdAutomatonBuilder, RuleBuilder},
        },
        lia_threshold_automaton::{
            ComparisonConstraint, ComparisonConstraintCreationError, ConstraintRewriteError,
            LIARule, LIAThresholdAutomaton, LIATransformationError, LIAVariableConstraint,
            SingleAtomConstraint, SumAtomConstraint, SumVarConstraintCreationError, WeightedSum,
            integer_thresholds::{
                Threshold, ThresholdCompOp, ThresholdConstraint, ThresholdConstraintOver,
            },
        },
    };

    #[test]
    fn test_lia_threshold_automaton_getters() {
        let rule = RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2")).build();

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
                rule.clone(),
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
                ) & LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            )
            .unwrap()
            .with_initial_variable_constraint(
                BooleanVarConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ) & BooleanVarConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("var2"))),
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

        let abstract_rule = LIARule {
            id: 0,
            source: Location::new("loc1"),
            target: Location::new("loc2"),
            guard: LIAVariableConstraint::True,
            actions: vec![],
        };

        let lta = LIAThresholdAutomaton {
            ta: ta.clone(),
            rules: HashMap::from([
                (Location::new("loc1"), vec![abstract_rule.clone()]),
                (
                    Location::new("loc2"),
                    vec![LIARule {
                        id: 1,
                        source: Location::new("loc2"),
                        target: Location::new("loc3"),
                        guard: (LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
                            ThresholdConstraintOver::new(
                                WeightedSum::new([(Variable::new("var1"), Fraction::from(1))]),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Lt,
                                    Vec::<(Parameter, Fraction)>::new(),
                                    2,
                                ),
                            ),
                        )) & LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
                            ThresholdConstraintOver::new(
                                WeightedSum::new([(Variable::new("var1"), Fraction::from(1))]),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Geq,
                                    Vec::<(Parameter, Fraction)>::new(),
                                    1,
                                ),
                            ),
                        ))) & (LIAVariableConstraint::SingleVarConstraint(
                            SingleAtomConstraint(ThresholdConstraintOver::new(
                                Variable::new("var2"),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Lt,
                                    [(Parameter::new("n"), 1)],
                                    1,
                                ),
                            )),
                        ) & LIAVariableConstraint::SingleVarConstraint(
                            SingleAtomConstraint(ThresholdConstraintOver::new(
                                Variable::new("var2"),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Geq,
                                    [(Parameter::new("n"), 1)],
                                    0,
                                ),
                            )),
                        )) | (LIAVariableConstraint::ComparisonConstraint(
                            ComparisonConstraint(ThresholdConstraintOver::new(
                                WeightedSum::new([
                                    (Variable::new("var1"), Fraction::from(1)),
                                    (Variable::new("var2"), -Fraction::from(1)),
                                ]),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Lt,
                                    Vec::<(Parameter, Fraction)>::new(),
                                    2,
                                ),
                            )),
                        ) & LIAVariableConstraint::ComparisonConstraint(
                            ComparisonConstraint(ThresholdConstraintOver::new(
                                WeightedSum::new([
                                    (Variable::new("var1"), Fraction::from(1)),
                                    (Variable::new("var2"), -Fraction::from(1)),
                                ]),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Geq,
                                    Vec::<(Parameter, Fraction)>::new(),
                                    1,
                                ),
                            )),
                        )),
                        actions: vec![
                            Action::new(Variable::new("var3"), IntegerExpression::Const(0))
                                .unwrap(),
                            Action::new(
                                Variable::new("var1"),
                                IntegerExpression::BinaryExpr(
                                    Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                                    IntegerOp::Add,
                                    Box::new(IntegerExpression::Const(1)),
                                ),
                            )
                            .unwrap(),
                        ],
                    }],
                ),
            ]),
            init_variable_constr: vec![LIAVariableConstraint::BinaryGuard(
                Box::new(
                    (LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint::new(
                        Variable::new("var1"),
                        ThresholdConstraint::new(
                            ThresholdCompOp::Leq,
                            Vec::<(Parameter, Fraction)>::new(),
                            0,
                        ),
                    ))) & LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint::new(
                        Variable::new("var1"),
                        ThresholdConstraint::new(
                            ThresholdCompOp::Geq,
                            Vec::<(Parameter, Fraction)>::new(),
                            0,
                        ),
                    )),
                ),
                BooleanConnective::And,
                Box::new(
                    LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint::new(
                        Variable::new("var2"),
                        ThresholdConstraint::new(
                            ThresholdCompOp::Leq,
                            Vec::<(Parameter, Fraction)>::new(),
                            0,
                        ),
                    )) & LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint::new(
                        Variable::new("var2"),
                        ThresholdConstraint::new(
                            ThresholdCompOp::Geq,
                            Vec::<(Parameter, Fraction)>::new(),
                            0,
                        ),
                    )),
                ),
            )],
            additional_vars_for_sums: HashMap::new(),
        };

        assert_eq!(lta.get_ta(), &ta);
        assert_eq!(lta.get_max_number_of_thresholds_per_rule(), 6);

        assert_eq!(lta.name(), "test_ta1");
        assert_eq!(lta.variables().count(), 3);
        assert!(lta.variables().all(|v| ta.variables().any(|tv| tv == v)));

        assert_eq!(lta.parameters().count(), 3);
        assert!(lta.parameters().all(|p| ta.parameters().any(|tp| tp == p)));

        assert_eq!(lta.locations().count(), 3);
        assert!(lta.locations().all(|l| ta.locations().any(|tl| tl == l)));

        assert_eq!(lta.resilience_conditions().count(), 1);
        assert!(
            lta.resilience_conditions()
                .all(|rc| ta.resilience_conditions().any(|trc| trc == rc))
        );

        assert!(lta.can_be_initial_location(&Location::new("loc1")));
        assert!(!lta.can_be_initial_location(&Location::new("loc2")));

        assert!(lta.outgoing_rules(&Location::new("loc3")).next().is_none());
        assert_eq!(lta.outgoing_rules(&Location::new("loc2")).count(), 1);
        assert_eq!(lta.incoming_rules(&Location::new("loc2")).count(), 1);
        assert_eq!(lta.incoming_rules(&Location::new("loc1")).count(), 0);

        let mut sorted_rules = lta.rules().cloned().collect::<Vec<_>>();
        sorted_rules.sort_by_key(|r| r.id());

        assert_eq!(
            lta.get_thresholds(),
            HashSet::from([
                Threshold::new(Vec::<(Parameter, Fraction)>::new(), 1),
                Threshold::new(Vec::<(Parameter, Fraction)>::new(), 2),
                Threshold::new([(Parameter::new("n"), 1)], 0),
                Threshold::new([(Parameter::new("n"), 1)], 1),
            ])
        );

        assert_eq!(
            sorted_rules,
            vec![
                LIARule {
                    id: 0,
                    source: Location::new("loc1"),
                    target: Location::new("loc2"),
                    guard: LIAVariableConstraint::True,
                    actions: vec![],
                },
                LIARule {
                    id: 1,
                    source: Location::new("loc2"),
                    target: Location::new("loc3"),
                    guard: (LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
                        ThresholdConstraintOver::new(
                            WeightedSum::new([(Variable::new("var1"), 1,)]),
                            ThresholdConstraint::new(
                                ThresholdCompOp::Lt,
                                Vec::<(Parameter, Fraction)>::new(),
                                2
                            ),
                        )
                    )) & LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
                        ThresholdConstraintOver::new(
                            WeightedSum::new([(Variable::new("var1"), 1,)]),
                            ThresholdConstraint::new(
                                ThresholdCompOp::Geq,
                                Vec::<(Parameter, Fraction)>::new(),
                                1
                            ),
                        )
                    ))) & (LIAVariableConstraint::SingleVarConstraint(
                        SingleAtomConstraint(ThresholdConstraintOver::new(
                            Variable::new("var2"),
                            ThresholdConstraint::new(
                                ThresholdCompOp::Lt,
                                [(Parameter::new("n"), 1)],
                                1
                            ),
                        ))
                    ) & LIAVariableConstraint::SingleVarConstraint(
                        SingleAtomConstraint(ThresholdConstraintOver::new(
                            Variable::new("var2"),
                            ThresholdConstraint::new(
                                ThresholdCompOp::Geq,
                                [(Parameter::new("n"), 1)],
                                0
                            ),
                        ))
                    )) | (LIAVariableConstraint::ComparisonConstraint(
                        ComparisonConstraint(ThresholdConstraintOver::new(
                            WeightedSum::new([
                                (Variable::new("var1"), Fraction::from(1)),
                                (Variable::new("var2"), -Fraction::from(1))
                            ]),
                            ThresholdConstraint::new(
                                ThresholdCompOp::Lt,
                                Vec::<(Parameter, Fraction)>::new(),
                                2,
                            ),
                        ))
                    ) & LIAVariableConstraint::ComparisonConstraint(
                        ComparisonConstraint(ThresholdConstraintOver::new(
                            WeightedSum::new([
                                (Variable::new("var1"), Fraction::from(1)),
                                (Variable::new("var2"), -Fraction::from(1))
                            ]),
                            ThresholdConstraint::new(
                                ThresholdCompOp::Geq,
                                Vec::<(Parameter, Fraction)>::new(),
                                1,
                            ),
                        ))
                    )),
                    actions: vec![
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
                    ],
                }
            ]
        );

        assert_eq!(lta.get_derived_rule(&abstract_rule), rule);

        assert_eq!(lta.initial_location_constraints().count(), 1);
        assert!(
            lta.initial_location_constraints()
                .any(|ilc| ta.initial_location_constraints().any(|tilc| tilc == ilc))
        );

        assert_eq!(lta.initial_variable_constraints().count(), 1);
        assert!(lta.initial_variable_constraints().any(|ivc| {
            ta.initial_variable_constraints()
                .map(|c| LIAVariableConstraint::try_from(c.remove_boolean_negations()).unwrap())
                .any(|tivc| tivc == *ivc)
        }));
    }

    #[test]
    fn test_lia_get_single_var_threshold() {
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

        let lta = LIAThresholdAutomaton {
            ta,
            rules: HashMap::from([
                (
                    Location::new("loc1"),
                    vec![LIARule {
                        id: 0,
                        source: Location::new("loc1"),
                        target: Location::new("loc2"),
                        guard: LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint(
                            ThresholdConstraintOver::new(
                                Variable::new("var1"),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Lt,
                                    Vec::<(Parameter, Fraction)>::new(),
                                    2,
                                ),
                            ),
                        )) & LIAVariableConstraint::SingleVarConstraint(
                            SingleAtomConstraint(ThresholdConstraintOver::new(
                                Variable::new("var1"),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Geq,
                                    Vec::<(Parameter, Fraction)>::new(),
                                    1,
                                ),
                            )),
                        ),
                        actions: vec![],
                    }],
                ),
                (
                    Location::new("loc2"),
                    vec![LIARule {
                        id: 1,
                        source: Location::new("loc2"),
                        target: Location::new("loc3"),
                        guard: (LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint(
                            ThresholdConstraintOver::new(
                                Variable::new("var1"),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Lt,
                                    Vec::<(Parameter, Fraction)>::new(),
                                    2,
                                ),
                            ),
                        )) & LIAVariableConstraint::SingleVarConstraint(
                            SingleAtomConstraint(ThresholdConstraintOver::new(
                                Variable::new("var1"),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Geq,
                                    Vec::<(Parameter, Fraction)>::new(),
                                    1,
                                ),
                            )),
                        )) & (LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
                            ThresholdConstraintOver::new(
                                WeightedSum::new(BTreeMap::from([
                                    (Variable::new("var2"), 1),
                                    (Variable::new("var1"), 1),
                                ])),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Lt,
                                    BTreeMap::from([(Parameter::new("n"), 1)]),
                                    1,
                                ),
                            ),
                        )) & LIAVariableConstraint::SumVarConstraint(
                            SumAtomConstraint(ThresholdConstraintOver::new(
                                WeightedSum::new(BTreeMap::from([
                                    (Variable::new("var2"), 1),
                                    (Variable::new("var1"), 1),
                                ])),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Geq,
                                    BTreeMap::from([(Parameter::new("n"), 1)]),
                                    0,
                                ),
                            )),
                        )) | (LIAVariableConstraint::ComparisonConstraint(
                            ComparisonConstraint(ThresholdConstraintOver::new(
                                WeightedSum::new(BTreeMap::from([
                                    (Variable::new("var3"), 1.into()),
                                    (Variable::new("var3"), -Fraction::from(1)),
                                ])),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Lt,
                                    BTreeMap::from([(Parameter::new("t"), 3)]),
                                    1,
                                ),
                            )),
                        ) & LIAVariableConstraint::ComparisonConstraint(
                            ComparisonConstraint(ThresholdConstraintOver::new(
                                WeightedSum::new(BTreeMap::from([
                                    (Variable::new("var3"), 1.into()),
                                    (Variable::new("var3"), -Fraction::from(1)),
                                ])),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Geq,
                                    BTreeMap::from([(Parameter::new("t"), 3)]),
                                    0,
                                ),
                            )),
                        )),
                        actions: vec![
                            Action::new(Variable::new("var3"), IntegerExpression::Const(0))
                                .unwrap(),
                            Action::new(
                                Variable::new("var1"),
                                IntegerExpression::BinaryExpr(
                                    Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                                    IntegerOp::Add,
                                    Box::new(IntegerExpression::Const(1)),
                                ),
                            )
                            .unwrap(),
                        ],
                    }],
                ),
            ]),
            init_variable_constr: vec![],
            additional_vars_for_sums: HashMap::new(),
        };

        let expected = HashSet::from([
            SingleAtomConstraint(ThresholdConstraintOver::new(
                Variable::new("var1"),
                ThresholdConstraint::new(
                    ThresholdCompOp::Lt,
                    Vec::<(Parameter, Fraction)>::new(),
                    2,
                ),
            )),
            SingleAtomConstraint(ThresholdConstraintOver::new(
                Variable::new("var1"),
                ThresholdConstraint::new(
                    ThresholdCompOp::Geq,
                    Vec::<(Parameter, Fraction)>::new(),
                    1,
                ),
            )),
        ]);
        assert_eq!(lta.get_single_var_constraints_rules(), expected)
    }

    #[test]
    fn test_lia_ta_has_comparison_guard() {
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

        let lta = LIAThresholdAutomaton {
            ta,
            rules: HashMap::from([
                (
                    Location::new("loc1"),
                    vec![LIARule {
                        id: 0,
                        source: Location::new("loc1"),
                        target: Location::new("loc2"),
                        guard: LIAVariableConstraint::True,
                        actions: vec![],
                    }],
                ),
                (
                    Location::new("loc2"),
                    vec![LIARule {
                        id: 1,
                        source: Location::new("loc2"),
                        target: Location::new("loc3"),
                        guard: (LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint(
                            ThresholdConstraintOver::new(
                                Variable::new("var1"),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Lt,
                                    Vec::<(Parameter, Fraction)>::new(),
                                    2,
                                ),
                            ),
                        )) & LIAVariableConstraint::SingleVarConstraint(
                            SingleAtomConstraint(ThresholdConstraintOver::new(
                                Variable::new("var1"),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Geq,
                                    Vec::<(Parameter, Fraction)>::new(),
                                    1,
                                ),
                            )),
                        )) & (LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
                            ThresholdConstraintOver::new(
                                WeightedSum::new(BTreeMap::from([
                                    (Variable::new("var2"), 1),
                                    (Variable::new("var1"), 1),
                                ])),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Lt,
                                    BTreeMap::from([(Parameter::new("n"), 1)]),
                                    1,
                                ),
                            ),
                        )) & LIAVariableConstraint::SumVarConstraint(
                            SumAtomConstraint(ThresholdConstraintOver::new(
                                WeightedSum::new(BTreeMap::from([
                                    (Variable::new("var2"), 1),
                                    (Variable::new("var1"), 1),
                                ])),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Geq,
                                    BTreeMap::from([(Parameter::new("n"), 1)]),
                                    0,
                                ),
                            )),
                        )) | (LIAVariableConstraint::ComparisonConstraint(
                            ComparisonConstraint(ThresholdConstraintOver::new(
                                WeightedSum::new(BTreeMap::from([
                                    (Variable::new("var3"), 1.into()),
                                    (Variable::new("var3"), -Fraction::from(1)),
                                ])),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Lt,
                                    BTreeMap::from([(Parameter::new("t"), 3)]),
                                    1,
                                ),
                            )),
                        ) & LIAVariableConstraint::ComparisonConstraint(
                            ComparisonConstraint(ThresholdConstraintOver::new(
                                WeightedSum::new(BTreeMap::from([
                                    (Variable::new("var3"), 1.into()),
                                    (Variable::new("var3"), -Fraction::from(1)),
                                ])),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Geq,
                                    BTreeMap::from([(Parameter::new("t"), 3)]),
                                    0,
                                ),
                            )),
                        )),
                        actions: vec![
                            Action::new(Variable::new("var3"), IntegerExpression::Const(0))
                                .unwrap(),
                            Action::new(
                                Variable::new("var1"),
                                IntegerExpression::BinaryExpr(
                                    Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                                    IntegerOp::Add,
                                    Box::new(IntegerExpression::Const(1)),
                                ),
                            )
                            .unwrap(),
                        ],
                    }],
                ),
            ]),
            init_variable_constr: vec![],
            additional_vars_for_sums: HashMap::new(),
        };

        assert!(lta.has_comparison_guard());
        let expected = HashSet::from([
            ComparisonConstraint(ThresholdConstraintOver::new(
                WeightedSum::new(BTreeMap::from([
                    (Variable::new("var3"), 1.into()),
                    (Variable::new("var3"), -Fraction::from(1)),
                ])),
                ThresholdConstraint::new(
                    ThresholdCompOp::Lt,
                    BTreeMap::from([(Parameter::new("t"), 3)]),
                    1,
                ),
            )),
            ComparisonConstraint(ThresholdConstraintOver::new(
                WeightedSum::new(BTreeMap::from([
                    (Variable::new("var3"), 1.into()),
                    (Variable::new("var3"), -Fraction::from(1)),
                ])),
                ThresholdConstraint::new(
                    ThresholdCompOp::Geq,
                    BTreeMap::from([(Parameter::new("t"), 3)]),
                    0,
                ),
            )),
        ]);
        assert_eq!(lta.get_comparison_guards(), expected);

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

        let lta = LIAThresholdAutomaton {
            ta,
            rules: HashMap::from([
                (
                    Location::new("loc1"),
                    vec![LIARule {
                        id: 0,
                        source: Location::new("loc1"),
                        target: Location::new("loc2"),
                        guard: LIAVariableConstraint::True,
                        actions: vec![],
                    }],
                ),
                (
                    Location::new("loc2"),
                    vec![LIARule {
                        id: 1,
                        source: Location::new("loc2"),
                        target: Location::new("loc3"),
                        guard: (LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint(
                            ThresholdConstraintOver::new(
                                Variable::new("var1"),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Lt,
                                    Vec::<(Parameter, Fraction)>::new(),
                                    2,
                                ),
                            ),
                        )) & LIAVariableConstraint::SingleVarConstraint(
                            SingleAtomConstraint(ThresholdConstraintOver::new(
                                Variable::new("var1"),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Geq,
                                    Vec::<(Parameter, Fraction)>::new(),
                                    1,
                                ),
                            )),
                        )) & (LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
                            ThresholdConstraintOver::new(
                                WeightedSum::new(BTreeMap::from([
                                    (Variable::new("var2"), 1),
                                    (Variable::new("var1"), 1),
                                ])),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Lt,
                                    [(Parameter::new("n"), 1)],
                                    1,
                                ),
                            ),
                        )) & LIAVariableConstraint::SumVarConstraint(
                            SumAtomConstraint(ThresholdConstraintOver::new(
                                WeightedSum::new(BTreeMap::from([
                                    (Variable::new("var2"), 1),
                                    (Variable::new("var1"), 1),
                                ])),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Geq,
                                    [(Parameter::new("n"), 1)],
                                    0,
                                ),
                            )),
                        )),
                        actions: vec![
                            Action::new(Variable::new("var3"), IntegerExpression::Const(0))
                                .unwrap(),
                            Action::new(
                                Variable::new("var1"),
                                IntegerExpression::BinaryExpr(
                                    Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                                    IntegerOp::Add,
                                    Box::new(IntegerExpression::Const(1)),
                                ),
                            )
                            .unwrap(),
                        ],
                    }],
                ),
            ]),
            init_variable_constr: vec![],
            additional_vars_for_sums: HashMap::new(),
        };

        assert!(!lta.has_comparison_guard());
        assert!(lta.get_comparison_guards().is_empty());
    }

    #[test]
    fn test_lia_has_multi_var() {
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

        let lta = LIAThresholdAutomaton {
            ta,
            rules: HashMap::from([
                (
                    Location::new("loc1"),
                    vec![LIARule {
                        id: 0,
                        source: Location::new("loc1"),
                        target: Location::new("loc2"),
                        guard: LIAVariableConstraint::True,
                        actions: vec![],
                    }],
                ),
                (
                    Location::new("loc2"),
                    vec![LIARule {
                        id: 1,
                        source: Location::new("loc2"),
                        target: Location::new("loc3"),
                        guard: (LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint(
                            ThresholdConstraintOver::new(
                                Variable::new("var1"),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Lt,
                                    Vec::<(Parameter, Fraction)>::new(),
                                    2,
                                ),
                            ),
                        )) & LIAVariableConstraint::SingleVarConstraint(
                            SingleAtomConstraint(ThresholdConstraintOver::new(
                                Variable::new("var1"),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Geq,
                                    Vec::<(Parameter, Fraction)>::new(),
                                    1,
                                ),
                            )),
                        )) & (LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
                            ThresholdConstraintOver::new(
                                WeightedSum::new(BTreeMap::from([
                                    (Variable::new("var2"), 1),
                                    (Variable::new("var1"), 1),
                                ])),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Lt,
                                    BTreeMap::from([(Parameter::new("n"), 1)]),
                                    1,
                                ),
                            ),
                        )) & LIAVariableConstraint::SumVarConstraint(
                            SumAtomConstraint(ThresholdConstraintOver::new(
                                WeightedSum::new(BTreeMap::from([
                                    (Variable::new("var2"), 1),
                                    (Variable::new("var1"), 1),
                                ])),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Geq,
                                    BTreeMap::from([(Parameter::new("n"), 1)]),
                                    0,
                                ),
                            )),
                        )) | (LIAVariableConstraint::ComparisonConstraint(
                            ComparisonConstraint(ThresholdConstraintOver::new(
                                WeightedSum::new(BTreeMap::from([
                                    (Variable::new("var3"), 1.into()),
                                    (Variable::new("var3"), -Fraction::from(1)),
                                ])),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Lt,
                                    BTreeMap::from([(Parameter::new("t"), 3)]),
                                    1,
                                ),
                            )),
                        ) & LIAVariableConstraint::ComparisonConstraint(
                            ComparisonConstraint(ThresholdConstraintOver::new(
                                WeightedSum::new(BTreeMap::from([
                                    (Variable::new("var3"), 1.into()),
                                    (Variable::new("var3"), -Fraction::from(1)),
                                ])),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Geq,
                                    BTreeMap::from([(Parameter::new("t"), 3)]),
                                    0,
                                ),
                            )),
                        )),
                        actions: vec![
                            Action::new(Variable::new("var3"), IntegerExpression::Const(0))
                                .unwrap(),
                            Action::new(
                                Variable::new("var1"),
                                IntegerExpression::BinaryExpr(
                                    Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                                    IntegerOp::Add,
                                    Box::new(IntegerExpression::Const(1)),
                                ),
                            )
                            .unwrap(),
                        ],
                    }],
                ),
            ]),
            init_variable_constr: vec![],
            additional_vars_for_sums: HashMap::new(),
        };

        assert!(lta.has_sum_var_threshold_guard());

        let expected = HashSet::from([
            SumAtomConstraint(ThresholdConstraintOver::new(
                WeightedSum::new(BTreeMap::from([
                    (Variable::new("var2"), 1),
                    (Variable::new("var1"), 1),
                ])),
                ThresholdConstraint::new(
                    ThresholdCompOp::Geq,
                    BTreeMap::from([(Parameter::new("n"), 1)]),
                    0,
                ),
            )),
            SumAtomConstraint(ThresholdConstraintOver::new(
                WeightedSum::new(BTreeMap::from([
                    (Variable::new("var2"), 1),
                    (Variable::new("var1"), 1),
                ])),
                ThresholdConstraint::new(
                    ThresholdCompOp::Lt,
                    BTreeMap::from([(Parameter::new("n"), 1)]),
                    1,
                ),
            )),
        ]);
        assert_eq!(lta.get_sum_var_constraints(), expected);

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

        let lta = LIAThresholdAutomaton {
            ta,
            rules: HashMap::from([
                (
                    Location::new("loc1"),
                    vec![LIARule {
                        id: 0,
                        source: Location::new("loc1"),
                        target: Location::new("loc2"),
                        guard: LIAVariableConstraint::True,
                        actions: vec![],
                    }],
                ),
                (
                    Location::new("loc2"),
                    vec![LIARule {
                        id: 1,
                        source: Location::new("loc2"),
                        target: Location::new("loc3"),
                        guard: (LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint(
                            ThresholdConstraintOver::new(
                                Variable::new("var1"),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Lt,
                                    Vec::<(Parameter, Fraction)>::new(),
                                    2,
                                ),
                            ),
                        )) & LIAVariableConstraint::SingleVarConstraint(
                            SingleAtomConstraint(ThresholdConstraintOver::new(
                                Variable::new("var1"),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Geq,
                                    Vec::<(Parameter, Fraction)>::new(),
                                    1,
                                ),
                            )),
                        )) | (LIAVariableConstraint::ComparisonConstraint(
                            ComparisonConstraint(ThresholdConstraintOver::new(
                                WeightedSum::new(BTreeMap::from([
                                    (Variable::new("var3"), 1.into()),
                                    (Variable::new("var3"), -Fraction::from(1)),
                                ])),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Lt,
                                    BTreeMap::from([(Parameter::new("t"), 3)]),
                                    1,
                                ),
                            )),
                        ) & LIAVariableConstraint::ComparisonConstraint(
                            ComparisonConstraint(ThresholdConstraintOver::new(
                                WeightedSum::new(BTreeMap::from([
                                    (Variable::new("var3"), 1.into()),
                                    (Variable::new("var3"), -Fraction::from(1)),
                                ])),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Geq,
                                    BTreeMap::from([(Parameter::new("t"), 3)]),
                                    0,
                                ),
                            )),
                        )),
                        actions: vec![
                            Action::new(Variable::new("var3"), IntegerExpression::Const(0))
                                .unwrap(),
                            Action::new(
                                Variable::new("var1"),
                                IntegerExpression::BinaryExpr(
                                    Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                                    IntegerOp::Add,
                                    Box::new(IntegerExpression::Const(1)),
                                ),
                            )
                            .unwrap(),
                        ],
                    }],
                ),
            ]),
            init_variable_constr: vec![],
            additional_vars_for_sums: HashMap::new(),
        };

        assert!(!lta.has_sum_var_threshold_guard());
        assert!(lta.get_sum_var_constraints().is_empty());
    }

    #[test]
    fn test_lia_display() {
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
            .with_initial_variable_constraint(BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ))
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

        let lta = LIAThresholdAutomaton {
            ta,
            rules: HashMap::from([
                (
                    Location::new("loc1"),
                    vec![LIARule {
                        id: 0,
                        source: Location::new("loc1"),
                        target: Location::new("loc2"),
                        guard: LIAVariableConstraint::True,
                        actions: vec![],
                    }],
                ),
                (
                    Location::new("loc2"),
                    vec![LIARule {
                        id: 1,
                        source: Location::new("loc2"),
                        target: Location::new("loc3"),
                        guard: (LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint(
                            ThresholdConstraintOver::new(
                                Variable::new("var1"),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Lt,
                                    Vec::<(Parameter, Fraction)>::new(),
                                    2,
                                ),
                            ),
                        )) & LIAVariableConstraint::SingleVarConstraint(
                            SingleAtomConstraint(ThresholdConstraintOver::new(
                                Variable::new("var1"),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Geq,
                                    Vec::<(Parameter, Fraction)>::new(),
                                    1,
                                ),
                            )),
                        )) & (LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
                            ThresholdConstraintOver::new(
                                WeightedSum::new(BTreeMap::from([
                                    (Variable::new("var2"), 1),
                                    (Variable::new("var1"), 1),
                                ])),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Lt,
                                    BTreeMap::from([(Parameter::new("n"), 1)]),
                                    1,
                                ),
                            ),
                        )) & LIAVariableConstraint::SumVarConstraint(
                            SumAtomConstraint(ThresholdConstraintOver::new(
                                WeightedSum::new(BTreeMap::from([
                                    (Variable::new("var2"), 1),
                                    (Variable::new("var1"), 1),
                                ])),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Geq,
                                    BTreeMap::from([(Parameter::new("n"), 1)]),
                                    0,
                                ),
                            )),
                        )) | (LIAVariableConstraint::ComparisonConstraint(
                            ComparisonConstraint(ThresholdConstraintOver::new(
                                WeightedSum::new(BTreeMap::from([
                                    (Variable::new("var3"), 1.into()),
                                    (Variable::new("var3"), -Fraction::from(1)),
                                ])),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Lt,
                                    BTreeMap::from([(Parameter::new("t"), 3)]),
                                    1,
                                ),
                            )),
                        ) & LIAVariableConstraint::ComparisonConstraint(
                            ComparisonConstraint(ThresholdConstraintOver::new(
                                WeightedSum::new(BTreeMap::from([
                                    (Variable::new("var3"), 1.into()),
                                    (Variable::new("var3"), -Fraction::from(1)),
                                ])),
                                ThresholdConstraint::new(
                                    ThresholdCompOp::Geq,
                                    BTreeMap::from([(Parameter::new("t"), 3)]),
                                    0,
                                ),
                            )),
                        )),

                        actions: vec![
                            Action::new(Variable::new("var3"), IntegerExpression::Const(0))
                                .unwrap(),
                            Action::new(
                                Variable::new("var1"),
                                IntegerExpression::BinaryExpr(
                                    Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                                    IntegerOp::Add,
                                    Box::new(IntegerExpression::Const(1)),
                                ),
                            )
                            .unwrap(),
                        ],
                    }],
                ),
            ]),
            init_variable_constr: vec![
                LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint(
                    ThresholdConstraintOver::new(
                        Variable::new("var1"),
                        ThresholdConstraint::new(
                            ThresholdCompOp::Lt,
                            Vec::<(Parameter, Fraction)>::new(),
                            Fraction::from(2),
                        ),
                    ),
                )),
                LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint(
                    ThresholdConstraintOver::new(
                        Variable::new("var1"),
                        ThresholdConstraint::new(
                            ThresholdCompOp::Geq,
                            Vec::<(Parameter, Fraction)>::new(),
                            Fraction::from(1),
                        ),
                    ),
                )),
            ],
            additional_vars_for_sums: HashMap::new(),
        };

        let expected = "thresholdAutomaton test_ta1 {\n    shared var1, var2, var3;\n\n    parameters f, n, t;\n\n    assumptions (1) {\n        n > (3 * f);\n    }\n\n    locations (3) {\n        loc1:[0];\n        loc2:[1];\n        loc3:[2];\n    }\n\n    inits (3) {\n        (loc1 == (n - f) || loc2 == 0);\n        var1 < 2;\n        var1 >= 1;\n    }\n\n    rules (2) {\n        0: loc1 -> loc2\n            when ( true )\n            do {  };\n        1: loc2 -> loc3\n            when ( (((var1 < 2) && (var1 >= 1)) && ((var1 + var2 < n + 1) && (var1 + var2 >= n))) || ((-1 * var3 < 3 * t + 1) && (-1 * var3 >= 3 * t)) )\n            do { var3' == 0; var1' == var1 + 1 };\n    }\n}\n";

        assert_eq!(lta.to_string(), expected)
    }

    #[test]
    fn test_lia_rule_getters() {
        let rule = LIARule {
            id: 0,
            source: Location::new("loc1"),
            target: Location::new("loc2"),
            guard: LIAVariableConstraint::True,
            actions: vec![],
        };

        assert_eq!(rule.id(), 0);
        assert_eq!(rule.source(), &Location::new("loc1"));
        assert_eq!(rule.target(), &Location::new("loc2"));
        assert_eq!(rule.guard(), &LIAVariableConstraint::True);
        assert_eq!(rule.actions().count(), 0);
        assert_eq!(rule.number_of_updates(), 0);
        assert!(!rule.has_resets());
        assert!(!rule.has_decrements());

        let rule = LIARule {
            id: 0,
            source: Location::new("loc1"),
            target: Location::new("loc2"),
            guard: LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
                ThresholdConstraintOver::new(
                    WeightedSum::new(BTreeMap::from([(Variable::new("var1"), 1)])),
                    ThresholdConstraint::new(
                        ThresholdCompOp::Lt,
                        Vec::<(Parameter, Fraction)>::new(),
                        2,
                    ),
                ),
            )) & LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
                ThresholdConstraintOver::new(
                    WeightedSum::new(BTreeMap::from([(Variable::new("var1"), 1)])),
                    ThresholdConstraint::new(
                        ThresholdCompOp::Geq,
                        Vec::<(Parameter, Fraction)>::new(),
                        1,
                    ),
                ),
            )),
            actions: vec![
                Action::new(
                    Variable::new("var1"),
                    IntegerExpression::Atom(Variable::new("var1")) - IntegerExpression::Const(1),
                )
                .unwrap(),
            ],
        };

        assert_eq!(rule.id(), 0);
        assert_eq!(rule.source(), &Location::new("loc1"));
        assert_eq!(rule.target(), &Location::new("loc2"));
        assert_eq!(
            rule.guard(),
            &(LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
                ThresholdConstraintOver::new(
                    WeightedSum::new(BTreeMap::from([(Variable::new("var1"), 1)])),
                    ThresholdConstraint::new(
                        ThresholdCompOp::Lt,
                        Vec::<(Parameter, Fraction)>::new(),
                        2,
                    ),
                ),
            )) & LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
                ThresholdConstraintOver::new(
                    WeightedSum::new(BTreeMap::from([(Variable::new("var1"), 1)])),
                    ThresholdConstraint::new(
                        ThresholdCompOp::Geq,
                        Vec::<(Parameter, Fraction)>::new(),
                        1,
                    ),
                ),
            ))),
        );
        assert_eq!(
            rule.actions().cloned().collect::<Vec<_>>(),
            vec![
                Action::new(
                    Variable::new("var1"),
                    IntegerExpression::Atom(Variable::new("var1")) - IntegerExpression::Const(1)
                )
                .unwrap()
            ]
        );
        assert_eq!(rule.number_of_updates(), 1);
        assert!(!rule.has_resets());
        assert!(rule.has_decrements());

        let rule = LIARule {
            id: 2,
            source: Location::new("loc1"),
            target: Location::new("loc2"),
            guard: (LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
                ThresholdConstraintOver::new(
                    WeightedSum::new(BTreeMap::from([(Variable::new("var1"), 1)])),
                    ThresholdConstraint::new(
                        ThresholdCompOp::Lt,
                        Vec::<(Parameter, Fraction)>::new(),
                        2,
                    ),
                ),
            )) & LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
                ThresholdConstraintOver::new(
                    WeightedSum::new(BTreeMap::from([(Variable::new("var1"), 1)])),
                    ThresholdConstraint::new(
                        ThresholdCompOp::Geq,
                        Vec::<(Parameter, Fraction)>::new(),
                        1,
                    ),
                ),
            ))),
            actions: vec![Action::new(Variable::new("var1"), IntegerExpression::Const(0)).unwrap()],
        };

        assert_eq!(rule.id(), 2);
        assert_eq!(rule.source(), &Location::new("loc1"));
        assert_eq!(rule.target(), &Location::new("loc2"));
        assert_eq!(
            rule.guard(),
            &(LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
                ThresholdConstraintOver::new(
                    WeightedSum::new(BTreeMap::from([(Variable::new("var1"), 1)])),
                    ThresholdConstraint::new(
                        ThresholdCompOp::Lt,
                        Vec::<(Parameter, Fraction)>::new(),
                        2,
                    ),
                ),
            )) & LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
                ThresholdConstraintOver::new(
                    WeightedSum::new(BTreeMap::from([(Variable::new("var1"), 1)])),
                    ThresholdConstraint::new(
                        ThresholdCompOp::Geq,
                        Vec::<(Parameter, Fraction)>::new(),
                        1,
                    ),
                ),
            )))
        );
        assert_eq!(
            rule.actions().cloned().collect::<Vec<_>>(),
            vec![Action::new(Variable::new("var1"), IntegerExpression::Const(0)).unwrap()]
        );
        assert_eq!(rule.number_of_updates(), 1);
        assert!(rule.has_resets());
        assert!(!rule.has_decrements());
    }

    #[test]
    fn test_count_number_of_thresholds() {
        let thr = LIAVariableConstraint::False;
        assert_eq!(thr.count_number_of_thresholds(), 0);

        let thr = LIAVariableConstraint::True;
        assert_eq!(thr.count_number_of_thresholds(), 0);

        let thr = LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
            ThresholdConstraintOver::new(
                WeightedSum::new(BTreeMap::from([(Variable::new("var1"), 1)])),
                ThresholdConstraint::new(
                    ThresholdCompOp::Lt,
                    Vec::<(Parameter, Fraction)>::new(),
                    2,
                ),
            ),
        )) & LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
            ThresholdConstraintOver::new(
                WeightedSum::new(BTreeMap::from([(Variable::new("var1"), 1)])),
                ThresholdConstraint::new(
                    ThresholdCompOp::Geq,
                    Vec::<(Parameter, Fraction)>::new(),
                    1,
                ),
            ),
        ));
        assert_eq!(thr.count_number_of_thresholds(), 2);

        let thr = LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
            ThresholdConstraintOver::new(
                WeightedSum::new(BTreeMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                ])),
                ThresholdConstraint::new(
                    ThresholdCompOp::Lt,
                    BTreeMap::from([(Parameter::new("n"), 3)]),
                    6,
                ),
            ),
        )) & LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
            ThresholdConstraintOver::new(
                WeightedSum::new(BTreeMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                ])),
                ThresholdConstraint::new(
                    ThresholdCompOp::Geq,
                    BTreeMap::from([(Parameter::new("n"), 3)]),
                    5,
                ),
            ),
        ));
        assert_eq!(thr.count_number_of_thresholds(), 2);

        let thr = (LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
            ThresholdConstraintOver::new(
                WeightedSum::new(BTreeMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                ])),
                ThresholdConstraint::new(
                    ThresholdCompOp::Lt,
                    BTreeMap::from([(Parameter::new("n"), 3)]),
                    1,
                ),
            ),
        )) & LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
            ThresholdConstraintOver::new(
                WeightedSum::new(BTreeMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                ])),
                ThresholdConstraint::new(
                    ThresholdCompOp::Geq,
                    BTreeMap::from([(Parameter::new("n"), 3)]),
                    0,
                ),
            ),
        ))) | (LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
            ThresholdConstraintOver::new(
                WeightedSum::new(BTreeMap::from([(Variable::new("var3"), 1)])),
                ThresholdConstraint::new(
                    ThresholdCompOp::Lt,
                    BTreeMap::from([(Parameter::new("m"), 3)]),
                    1,
                ),
            ),
        )) & LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
            ThresholdConstraintOver::new(
                WeightedSum::new(BTreeMap::from([(Variable::new("var3"), 1)])),
                ThresholdConstraint::new(
                    ThresholdCompOp::Geq,
                    BTreeMap::from([(Parameter::new("m"), 3)]),
                    0,
                ),
            ),
        )));
        assert_eq!(thr.count_number_of_thresholds(), 4);
    }

    #[test]
    fn test_bin_op_threshold_guard() {
        let thr = LIAVariableConstraint::False & LIAVariableConstraint::True;
        assert_eq!(
            thr,
            LIAVariableConstraint::BinaryGuard(
                Box::new(LIAVariableConstraint::False),
                BooleanConnective::And,
                Box::new(LIAVariableConstraint::True)
            )
        );

        let thr = LIAVariableConstraint::False | LIAVariableConstraint::True;
        assert_eq!(
            thr,
            LIAVariableConstraint::BinaryGuard(
                Box::new(LIAVariableConstraint::False),
                BooleanConnective::Or,
                Box::new(LIAVariableConstraint::True)
            )
        );
    }

    #[test]
    fn test_is_top() {
        assert!(LIAVariableConstraint::True.is_top());
        assert!(!LIAVariableConstraint::False.is_top());

        // A conjunction is top only if both conjuncts are top
        let guard = LIAVariableConstraint::True & LIAVariableConstraint::True;
        assert!(guard.is_top());

        let guard = LIAVariableConstraint::True & LIAVariableConstraint::False;
        assert!(!guard.is_top());

        // A disjunction is top if at least one disjunct is top
        let guard = LIAVariableConstraint::False | LIAVariableConstraint::True;
        assert!(guard.is_top());

        let guard = LIAVariableConstraint::False | LIAVariableConstraint::False;
        assert!(!guard.is_top());

        // Propagation through nested binary guards
        let guard = (LIAVariableConstraint::True & LIAVariableConstraint::False)
            | LIAVariableConstraint::True;
        assert!(guard.is_top());

        // Atomic constraints are never top (no semantic analysis)
        let guard = LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint::new(
            Variable::new("var1"),
            ThresholdConstraint::new(ThresholdCompOp::Geq, Vec::<(Parameter, Fraction)>::new(), 0),
        ));
        assert!(!guard.is_top());
    }

    #[test]
    fn test_is_bot() {
        assert!(LIAVariableConstraint::False.is_bot());
        assert!(!LIAVariableConstraint::True.is_bot());

        // A conjunction is bot if at least one conjunct is bot
        let guard = LIAVariableConstraint::False & LIAVariableConstraint::True;
        assert!(guard.is_bot());

        let guard = LIAVariableConstraint::True & LIAVariableConstraint::True;
        assert!(!guard.is_bot());

        // A disjunction is bot only if both disjuncts are bot
        let guard = LIAVariableConstraint::False | LIAVariableConstraint::False;
        assert!(guard.is_bot());

        let guard = LIAVariableConstraint::False | LIAVariableConstraint::True;
        assert!(!guard.is_bot());

        // Propagation through nested binary guards
        let guard = (LIAVariableConstraint::True | LIAVariableConstraint::False)
            & LIAVariableConstraint::False;
        assert!(guard.is_bot());

        // Atomic constraints are never bot (no semantic analysis)
        let guard = LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint::new(
            Variable::new("var1"),
            ThresholdConstraint::new(ThresholdCompOp::Geq, Vec::<(Parameter, Fraction)>::new(), 0),
        ));
        assert!(!guard.is_bot());
    }

    #[test]
    fn test_guards_to_boolean() {
        let guard = LIAVariableConstraint::True;
        assert_eq!(guard.as_boolean_expr(), BooleanExpression::True);

        let guard = LIAVariableConstraint::False;
        assert_eq!(guard.as_boolean_expr(), BooleanExpression::False);

        let guard = LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint(
            ThresholdConstraintOver::new(
                Variable::new("var1"),
                ThresholdConstraint::new(
                    ThresholdCompOp::Lt,
                    Vec::<(Parameter, Fraction)>::new(),
                    1,
                ),
            ),
        ));
        assert_eq!(
            guard.as_boolean_expr(),
            BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Lt,
                Box::new(IntegerExpression::Const(1))
            )
        );

        let guard = LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
            ThresholdConstraintOver::new(
                WeightedSum::new([(Variable::new("var1"), 1), (Variable::new("var2"), 2)]),
                ThresholdConstraint::new(
                    ThresholdCompOp::Lt,
                    BTreeMap::from([(Parameter::new("n"), 3)]),
                    5,
                ),
            ),
        ));
        assert_eq!(
            guard.as_boolean_expr(),
            BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                    IntegerOp::Add,
                    Box::new(IntegerExpression::BinaryExpr(
                        Box::new(IntegerExpression::Const(2)),
                        IntegerOp::Mul,
                        Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                    ))
                )),
                ComparisonOp::Lt,
                Box::new(
                    IntegerExpression::BinaryExpr(
                        Box::new(IntegerExpression::Const(3)),
                        IntegerOp::Mul,
                        Box::new(IntegerExpression::Param(Parameter::new("n")))
                    ) + IntegerExpression::Const(5)
                )
            )
        );

        let guard = LIAVariableConstraint::ComparisonConstraint(ComparisonConstraint(
            ThresholdConstraintOver::new(
                WeightedSum::new([
                    (Variable::new("var1"), 1.into()),
                    (Variable::new("var2"), Fraction::from(2)),
                ]),
                ThresholdConstraint::new(
                    ThresholdCompOp::Lt,
                    BTreeMap::from([(Parameter::new("n"), 3)]),
                    1,
                ),
            ),
        ));
        assert_eq!(
            guard.as_boolean_expr(),
            BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                    IntegerOp::Add,
                    Box::new(IntegerExpression::BinaryExpr(
                        Box::new(IntegerExpression::Const(2)),
                        IntegerOp::Mul,
                        Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                    ))
                )),
                ComparisonOp::Lt,
                Box::new(
                    IntegerExpression::BinaryExpr(
                        Box::new(IntegerExpression::Const(3)),
                        IntegerOp::Mul,
                        Box::new(IntegerExpression::Param(Parameter::new("n")))
                    ) + IntegerExpression::Const(1)
                )
            )
        );

        let guard = LIAVariableConstraint::BinaryGuard(
            Box::new(LIAVariableConstraint::True),
            BooleanConnective::And,
            Box::new(LIAVariableConstraint::False),
        );
        assert_eq!(
            guard.as_boolean_expr(),
            BooleanExpression::BinaryExpression(
                Box::new(BooleanExpression::True),
                BooleanConnective::And,
                Box::new(BooleanExpression::False)
            )
        );

        let guard = LIAVariableConstraint::BinaryGuard(
            Box::new(LIAVariableConstraint::True),
            BooleanConnective::Or,
            Box::new(LIAVariableConstraint::False),
        );
        assert_eq!(
            guard.as_boolean_expr(),
            BooleanExpression::BinaryExpression(
                Box::new(BooleanExpression::True),
                BooleanConnective::Or,
                Box::new(BooleanExpression::False)
            )
        );
    }

    #[test]
    fn test_threshold_guard_display() {
        let thr = LIAVariableConstraint::False;
        let expected = "false";
        assert_eq!(thr.to_string(), expected);

        let thr = LIAVariableConstraint::True;
        let expected = "true";
        assert_eq!(thr.to_string(), expected);

        let thr = LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
            ThresholdConstraintOver::new(
                WeightedSum::new(BTreeMap::from([(Variable::new("var1"), 1)])),
                ThresholdConstraint::new(
                    ThresholdCompOp::Lt,
                    Vec::<(Parameter, Fraction)>::new(),
                    1,
                ),
            ),
        ));
        let expected = "var1 < 1";
        assert_eq!(thr.to_string(), expected);

        let thr = LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
            ThresholdConstraintOver::new(
                WeightedSum::new(BTreeMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                ])),
                ThresholdConstraint::new(
                    ThresholdCompOp::Lt,
                    BTreeMap::from([(Parameter::new("n"), 3)]),
                    5,
                ),
            ),
        ));
        let expected = "var1 + 2 * var2 < 3 * n + 5";
        assert_eq!(thr.to_string(), expected);

        let thr = LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
            ThresholdConstraintOver::new(
                WeightedSum::new(BTreeMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                ])),
                ThresholdConstraint::new(
                    ThresholdCompOp::Lt,
                    BTreeMap::from([(Parameter::new("n"), 3)]),
                    0,
                ),
            ),
        )) & LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
            ThresholdConstraintOver::new(
                WeightedSum::new(BTreeMap::from([(Variable::new("var3"), 1)])),
                ThresholdConstraint::new(
                    ThresholdCompOp::Lt,
                    BTreeMap::from([(Parameter::new("m"), 3), (Parameter::new("o"), 4)]),
                    0,
                ),
            ),
        ));
        let expected = "(var1 + 2 * var2 < 3 * n) && (var3 < 3 * m + 4 * o)";
        assert_eq!(thr.to_string(), expected);
    }

    #[test]
    fn test_display_single_var_threshold_guard() {
        let guard = SingleAtomConstraint::new(
            Variable::new("var1"),
            ThresholdConstraint::new(ThresholdCompOp::Geq, Vec::<(Parameter, Fraction)>::new(), 5),
        );
        let expected = "var1 >= 5";
        assert_eq!(guard.to_string(), expected);
    }

    #[test]
    fn test_new_multi_var_threshold() {
        let guard = SumAtomConstraint::try_new(
            [(Variable::new("var1"), 1), (Variable::new("var2"), 2)],
            ThresholdConstraint::new(
                ThresholdCompOp::Geq,
                BTreeMap::from([(Parameter::new("n"), 3)]),
                5,
            ),
        )
        .unwrap();

        let expected = SumAtomConstraint(ThresholdConstraintOver::new(
            WeightedSum::new(BTreeMap::from([
                (Variable::new("var1"), 1),
                (Variable::new("var2"), 2),
            ])),
            ThresholdConstraint::new(ThresholdCompOp::Geq, [(Parameter::new("n"), 3)], 5),
        ));

        assert_eq!(guard, expected);

        let expected_thr = Threshold::new([(Parameter::new("n"), 3)], 5);

        assert_eq!(guard.get_threshold(), &expected_thr);
        assert_eq!(
            guard.get_atoms(),
            &WeightedSum::new(BTreeMap::from([
                (Variable::new("var1"), 1),
                (Variable::new("var2"), 2),
            ]))
        );
    }

    #[test]
    fn test_new_multi_var_threshold_all_vars_neg() {
        // -1 * var1 + -2 * var2 >=  3 * n + 5
        let guard = SumAtomConstraint::try_new(
            BTreeMap::from([
                (Variable::new("var1"), -Fraction::from(1)),
                (Variable::new("var2"), -Fraction::from(2)),
            ]),
            ThresholdConstraint::new(
                ThresholdCompOp::Geq,
                BTreeMap::from([(Parameter::new("n"), 3)]),
                5,
            ),
        )
        .unwrap();

        // var1 + 2 * var2 =< -3 * n - 5
        let expected = SumAtomConstraint(ThresholdConstraintOver::new(
            WeightedSum::new(BTreeMap::from([
                (Variable::new("var1"), 1),
                (Variable::new("var2"), 2),
            ])),
            ThresholdConstraint::new(
                ThresholdCompOp::Leq,
                BTreeMap::from([(Parameter::new("n"), -Fraction::from(3))]),
                -Fraction::from(5),
            ),
        ));

        assert_eq!(guard, expected);
    }

    #[test]
    fn test_new_multi_var_threshold_err_single() {
        let guard = SumAtomConstraint::try_new(
            BTreeMap::from([(Variable::new("var1"), 1)]),
            ThresholdConstraint::new(
                ThresholdCompOp::Geq,
                BTreeMap::from([(Parameter::new("n"), 3)]),
                5,
            ),
        );

        assert!(matches!(
            guard.clone(),
            Err(SumVarConstraintCreationError::IsSingleAtomConstraint)
        ));
        assert!(
            guard
                .unwrap_err()
                .to_string()
                .contains("SingleVarThresholdGuard")
        );
    }

    #[test]
    fn test_new_multi_var_threshold_err_mixed() {
        let guard = SumAtomConstraint::try_new(
            BTreeMap::from([
                (Variable::new("var1"), 1.into()),
                (Variable::new("var2"), -Fraction::from(2)),
            ]),
            ThresholdConstraint::new(
                ThresholdCompOp::Geq,
                BTreeMap::from([(Parameter::new("n"), 3)]),
                5,
            ),
        );

        assert!(matches!(
            guard.clone(),
            Err(SumVarConstraintCreationError::IsComparisonConstraint)
        ));
        assert!(guard.unwrap_err().to_string().contains("ComparisonGuard"));
    }

    #[test]
    fn test_display_multi_var_threshold_guard() {
        let guard = SumAtomConstraint::try_new(
            BTreeMap::from([(Variable::new("var1"), 1), (Variable::new("var2"), 2)]),
            ThresholdConstraint::new(
                ThresholdCompOp::Geq,
                BTreeMap::from([(Parameter::new("n"), 3)]),
                5,
            ),
        )
        .unwrap();
        let expected = "var1 + 2 * var2 >= 3 * n + 5";
        assert_eq!(guard.to_string(), expected);
    }

    #[test]
    fn test_new_comparison_guard() {
        let guard = ComparisonConstraint::try_new(
            BTreeMap::from([
                (Variable::new("var1"), 1.into()),
                (Variable::new("var2"), -Fraction::from(2)),
            ]),
            ThresholdConstraint::new(
                ThresholdCompOp::Geq,
                BTreeMap::from([(Parameter::new("n"), 3)]),
                5,
            ),
        )
        .unwrap();

        let expected = ComparisonConstraint(ThresholdConstraintOver::new(
            WeightedSum::new(BTreeMap::from([
                (Variable::new("var1"), 1.into()),
                (Variable::new("var2"), -Fraction::from(2)),
            ])),
            ThresholdConstraint::new(
                ThresholdCompOp::Geq,
                BTreeMap::from([(Parameter::new("n"), 3)]),
                5,
            ),
        ));

        assert_eq!(guard, expected);
    }

    #[test]
    fn test_comparison_guard_get_threshold_constr() {
        let guard = ComparisonConstraint(ThresholdConstraintOver::new(
            WeightedSum::from([
                (Variable::new("var1"), 1.into()),
                (Variable::new("var2"), -Fraction::from(2)),
            ]),
            ThresholdConstraint::new(ThresholdCompOp::Geq, [(Parameter::new("n"), 3)], 5),
        ));

        assert_eq!(
            guard.get_threshold_constraint(),
            &ThresholdConstraint::new(ThresholdCompOp::Geq, [(Parameter::new("n"), 3)], 5)
        )
    }

    #[test]
    fn test_new_comparison_guard_err_multi() {
        let guard = ComparisonConstraint::try_new(
            BTreeMap::from([
                (Variable::new("var1"), 1.into()),
                (Variable::new("var2"), 2.into()),
            ]),
            ThresholdConstraint::new(
                ThresholdCompOp::Geq,
                BTreeMap::from([(Parameter::new("n"), 3)]),
                5,
            ),
        );

        assert!(matches!(
            guard.clone(),
            Err(ComparisonConstraintCreationError::IsSumVarConstraint)
        ));
        assert!(
            guard
                .unwrap_err()
                .to_string()
                .contains("MultiVarThresholdGuard")
        );
    }

    #[test]
    fn test_display_comparison_guard() {
        let guard = ComparisonConstraint::try_new(
            BTreeMap::from([
                (Variable::new("var1"), 1.into()),
                (Variable::new("var2"), -Fraction::from(2)),
            ]),
            ThresholdConstraint::new(
                ThresholdCompOp::Geq,
                BTreeMap::from([(Parameter::new("n"), 3)]),
                5,
            ),
        )
        .unwrap();
        let expected = "var1 + -2 * var2 >= 3 * n + 5";
        assert_eq!(guard.to_string(), expected);
    }

    #[test]
    fn test_lower_and_upper_guard() {
        let lower_thr = ThresholdConstraint::new(
            ThresholdCompOp::Geq,
            BTreeMap::from([(Parameter::new("n"), 3)]),
            5,
        );

        let upper_thr = ThresholdConstraint::new(
            ThresholdCompOp::Lt,
            BTreeMap::from([(Parameter::new("n"), 3)]),
            4,
        );

        let guard = LIAVariableConstraint::ComparisonConstraint(
            ComparisonConstraint::try_new(
                BTreeMap::from([
                    (Variable::new("var1"), 1.into()),
                    (Variable::new("var2"), -Fraction::from(2)),
                ]),
                lower_thr.clone(),
            )
            .unwrap(),
        );
        assert!(guard.is_lower_guard());
        assert!(!guard.is_upper_guard());

        let guard = LIAVariableConstraint::ComparisonConstraint(
            ComparisonConstraint::try_new(
                BTreeMap::from([
                    (Variable::new("var1"), 1.into()),
                    (Variable::new("var2"), -Fraction::from(2)),
                ]),
                upper_thr.clone(),
            )
            .unwrap(),
        );
        assert!(!guard.is_lower_guard());
        assert!(guard.is_upper_guard());

        let guard = SingleAtomConstraint::new(Variable::new("var1"), lower_thr.clone());
        assert!(guard.is_lower_guard());
        assert!(!guard.is_upper_guard());

        let guard = SingleAtomConstraint::new(Variable::new("var1"), upper_thr.clone());
        assert!(!guard.is_lower_guard());
        assert!(guard.is_upper_guard());

        let guard = LIAVariableConstraint::SumVarConstraint(
            SumAtomConstraint::try_new(
                BTreeMap::from([
                    (Variable::new("var1"), 1.into()),
                    (Variable::new("var2"), Fraction::from(2)),
                ]),
                lower_thr.clone(),
            )
            .unwrap(),
        );
        assert!(guard.is_lower_guard());
        assert!(!guard.is_upper_guard());

        let guard = LIAVariableConstraint::SumVarConstraint(
            SumAtomConstraint::try_new(
                BTreeMap::from([
                    (Variable::new("var1"), 1.into()),
                    (Variable::new("var2"), Fraction::from(2)),
                ]),
                upper_thr.clone(),
            )
            .unwrap(),
        );
        assert!(!guard.is_lower_guard());
        assert!(guard.is_upper_guard());

        let guard = LIAVariableConstraint::True;
        assert!(!guard.is_lower_guard());
        assert!(!guard.is_upper_guard());

        let guard = LIAVariableConstraint::False;
        assert!(!guard.is_lower_guard());
        assert!(!guard.is_upper_guard());

        let guard = LIAVariableConstraint::BinaryGuard(
            Box::new(LIAVariableConstraint::True),
            BooleanConnective::And,
            Box::new(LIAVariableConstraint::False),
        );
        assert!(!guard.is_lower_guard());
        assert!(!guard.is_upper_guard());

        let guard = LIAVariableConstraint::BinaryGuard(
            Box::new(LIAVariableConstraint::SingleVarConstraint(
                SingleAtomConstraint::new(Variable::new("var1"), lower_thr.clone()),
            )),
            BooleanConnective::Or,
            Box::new(LIAVariableConstraint::SingleVarConstraint(
                SingleAtomConstraint::new(Variable::new("var1"), upper_thr.clone()),
            )),
        );
        assert!(guard.is_lower_guard());
        assert!(guard.is_upper_guard());
    }

    #[test]
    fn test_getters_single_var_thr() {
        let guard = SingleAtomConstraint::new(
            Variable::new("var1"),
            ThresholdConstraint::new(ThresholdCompOp::Geq, Vec::<(Parameter, Fraction)>::new(), 5),
        );

        assert_eq!(guard.get_atom(), &Variable::new("var1"));
        assert_eq!(
            guard.get_threshold(),
            &Threshold::new(Vec::<(Parameter, Fraction)>::new(), 5)
        );
    }

    #[test]
    fn test_getters_multi_var_thr() {
        let guard = SumAtomConstraint::try_new(
            BTreeMap::from([(Variable::new("var1"), 1), (Variable::new("var2"), 2)]),
            ThresholdConstraint::new(
                ThresholdCompOp::Geq,
                BTreeMap::from([(Parameter::new("n"), 3)]),
                5,
            ),
        )
        .unwrap();

        assert_eq!(
            guard.get_atoms(),
            &WeightedSum::new(BTreeMap::from([
                (Variable::new("var1"), 1),
                (Variable::new("var2"), 2),
            ]))
        );
        assert_eq!(
            guard.get_threshold(),
            &Threshold::new(BTreeMap::from([(Parameter::new("n"), 3)]), 5,)
        );
    }

    #[test]
    fn test_display_lia_transformation_error() {
        let error = LIATransformationError::GuardError(
            Box::new(RuleBuilder::new(0, Location::new("l1"), Location::new("l2")).build()),
            Box::new(BooleanExpression::False),
            Box::new(ConstraintRewriteError::NotLinearArithmetic),
        );
        let expected = "Error while transforming guard false of rule 0: l1 -> l2\n    when ( true )\n    do {  }: Non linear integer arithmetic expression detected. Threshold automata only allow for linear arithmetic formula in their guards.";

        assert_eq!(error.to_string(), expected);

        let error = LIATransformationError::InitialConstraintError(
            Box::new(BooleanExpression::False),
            Box::new(ConstraintRewriteError::NotLinearArithmetic),
        );
        let expected = "Error while transforming initial constraint false into linear arithmetic: Non linear integer arithmetic expression detected. Threshold automata only allow for linear arithmetic formula in their guards.";
        assert_eq!(error.to_string(), expected);
    }
}
