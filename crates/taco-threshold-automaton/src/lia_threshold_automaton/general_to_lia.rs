//! Logic to try to convert a [`GeneralThresholdAutomaton`] into a
//! [`LIAThresholdAutomaton`].
//!
//! This module contains the logic to transform a [`GeneralThresholdAutomaton`]
//! into a  [`LIAThresholdAutomaton`], i.e., into a threshold automaton where all
//! expressions are in linear arithmetic.
//!
//! The transformation works in the following way:
//!
//! First boolean negations are removed by pushing them inwards. This logic can
//! be found in the `remove_boolean_neg` module. This step converts
//! `BooleanExpression` into
//! `remove_boolean_neg::NonNegatedBooleanExpression`.
//!
//! Next, the integer expressions in the boolean expressions are transformed.
//! First, any subtractions are removed by transforming them into additions with
//! a negative number or by adding a factor `-1`. This logic can be found in the
//! `remove_minus` module. This step converts `IntegerExpressions` into
//! `NonMinusIntegerExpr`.
//!
//! Next, divisions are removed by transforming them into multiplications with
//! rational factors. This is the first incomplete step, as this is only
//! possible if there are no atoms appearing in a divisor. This logic can be
//! found in the `remove_div` module. This step converts
//! `NonMinusIntegerExpr` into `NonDivIntegerExpr`.
//!
//! If all expressions could be transformed we can now transform integer
//! expressions into weighted sums, with rational factors. This is the form
//! assumed by many papers in the formal definition of threshold automata. This
//! is done in the module `split_pairs`.
//!
//! The final step in processing integer expressions is to bring all variables
//! to the left side of the equation, and then classify them into the 3 LIAGuard
//! types. This logic can be found in the `classify_into_lia` module.
//!
//! Afterwards, the guards can finally be assembled back into the
//! [`LIAVariableConstraint`] type, which is a boolean combination of the 3
//! guard types.

use std::{collections::HashMap, error::Error, fmt::Display};

pub(crate) mod classify_into_lia;
mod remove_boolean_neg;
mod remove_div;
mod remove_minus;
mod split_pair;

use crate::{
    ActionDefinition, RuleDefinition,
    expressions::Location,
    general_threshold_automaton::{GeneralThresholdAutomaton, Rule},
};

use super::{
    ConstraintRewriteError, LIARule, LIAThresholdAutomaton, LIATransformationError,
    LIAVariableConstraint,
};

impl Error for ConstraintRewriteError {}

impl Display for ConstraintRewriteError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstraintRewriteError::NotLinearArithmetic => write!(
                f,
                "Non linear integer arithmetic expression detected. Threshold automata only allow for linear arithmetic formula in their guards.",
            ),
            ConstraintRewriteError::ParameterConstraint(expr) => write!(
                f,
                "Found a constraint over the parameter evaluation instead of the variable valuation ! The constraint {expr} restricts the parameter values, which is only allowed in the resilience condition."
            ),
        }
    }
}

impl TryFrom<GeneralThresholdAutomaton> for LIAThresholdAutomaton {
    type Error = LIATransformationError;

    fn try_from(ta: GeneralThresholdAutomaton) -> Result<Self, Self::Error> {
        let init_variable_constr = ta
            .initial_variable_conditions()
            .map(|c| {
                let c: LIAVariableConstraint = c.try_into().map_err(|err| {
                    LIATransformationError::InitialConstraintError(
                        Box::new(c.clone()),
                        Box::new(err),
                    )
                })?;

                Ok::<_, Self::Error>(c)
            })
            .collect::<Result<Vec<LIAVariableConstraint>, Self::Error>>()?;

        let rules: HashMap<Location, Vec<_>> = ta
            .get_rule_map()
            .into_iter()
            .map(|(loc, rules)| {
                let rules: Vec<LIARule> = rules
                    .into_iter()
                    .map(|r| LIARule::try_from(&r))
                    .collect::<Result<Vec<LIARule>, LIATransformationError>>()?;

                Ok::<(Location, Vec<LIARule>), LIATransformationError>((loc, rules))
            })
            .collect::<Result<HashMap<Location, Vec<_>>, LIATransformationError>>()?;

        Ok(Self {
            ta,
            init_variable_constr,
            rules,
            additional_vars_for_sums: HashMap::new(),
        })
    }
}

impl TryFrom<&Rule> for LIARule {
    type Error = LIATransformationError;

    /// Try to convert a rule into a [`LIARule`].
    ///
    /// A rule can be converted into a [`LIARule`] if the guard is a linear
    /// arithmetic formula. This means for example that it does not contain any
    /// multiplications between variables
    ///
    /// This function will return an [`LIATransformationError`] if the guard is
    /// no linear arithmetic formula.
    fn try_from(rule: &Rule) -> Result<Self, Self::Error> {
        let guard = rule.guard().try_into().map_err(|err| {
            LIATransformationError::GuardError(
                Box::new(rule.clone()),
                Box::new(rule.guard().clone()),
                Box::new(err),
            )
        })?;
        let actions = rule
            .actions()
            .filter(|ac| !ac.is_unchanged())
            .cloned()
            .collect();

        Ok(Self {
            id: rule.id(),
            source: rule.source().clone(),
            target: rule.target().clone(),
            guard,
            actions,
        })
    }
}

impl TryFrom<Rule> for LIARule {
    type Error = LIATransformationError;

    fn try_from(value: Rule) -> Result<Self, Self::Error> {
        (&value).try_into()
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::{
        BooleanVarConstraint, LocationConstraint, ParameterConstraint,
        expressions::{
            BooleanConnective, ComparisonOp, IntegerExpression, IntegerOp, Location, Parameter,
            Variable, fraction::Fraction,
        },
        general_threshold_automaton::{
            Action,
            builder::{GeneralThresholdAutomatonBuilder, RuleBuilder},
        },
        lia_threshold_automaton::{
            LIARule, LIAThresholdAutomaton, LIATransformationError, LIAVariableConstraint,
            SingleAtomConstraint,
            integer_thresholds::{ThresholdCompOp, ThresholdConstraint},
        },
    };

    #[test]
    fn test_full_ta_lia_ta() {
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
                ) | LocationConstraint::ComparisonExpression(
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
                    .with_actions(vec![
                        Action::new(
                            Variable::new("var1"),
                            IntegerExpression::Atom(Variable::new("var1")),
                        )
                        .unwrap(),
                    ])
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
                            Box::new(IntegerExpression::Param(Parameter::new("n"))),
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
            ])
            .unwrap()
            .build();

        let lia_ta = LIAThresholdAutomaton::try_from(ta.clone()).unwrap();

        let expected_lia = LIAThresholdAutomaton {
            ta: ta.clone(),
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
                        guard: LIAVariableConstraint::BinaryGuard(
                            Box::new(LIAVariableConstraint::BinaryGuard(
                                Box::new(LIAVariableConstraint::SingleVarConstraint(
                                    SingleAtomConstraint::new(
                                        Variable::new("var1"),
                                        ThresholdConstraint::new(
                                            ThresholdCompOp::Leq,
                                            Vec::<(Parameter, Fraction)>::new(),
                                            1,
                                        ),
                                    ),
                                )),
                                BooleanConnective::And,
                                Box::new(LIAVariableConstraint::SingleVarConstraint(
                                    SingleAtomConstraint::new(
                                        Variable::new("var1"),
                                        ThresholdConstraint::new(
                                            ThresholdCompOp::Geq,
                                            Vec::<(Parameter, Fraction)>::new(),
                                            1,
                                        ),
                                    ),
                                )),
                            )),
                            BooleanConnective::And,
                            Box::new(LIAVariableConstraint::BinaryGuard(
                                Box::new(LIAVariableConstraint::SingleVarConstraint(
                                    SingleAtomConstraint::new(
                                        Variable::new("var2"),
                                        ThresholdConstraint::new(
                                            ThresholdCompOp::Leq,
                                            [(Parameter::new("n"), 1)],
                                            0,
                                        ),
                                    ),
                                )),
                                BooleanConnective::And,
                                Box::new(LIAVariableConstraint::SingleVarConstraint(
                                    SingleAtomConstraint::new(
                                        Variable::new("var2"),
                                        ThresholdConstraint::new(
                                            ThresholdCompOp::Geq,
                                            [(Parameter::new("n"), 1)],
                                            0,
                                        ),
                                    ),
                                )),
                            )),
                        ),
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
                Box::new(LIAVariableConstraint::SingleVarConstraint(
                    SingleAtomConstraint::new(
                        Variable::new("var1"),
                        ThresholdConstraint::new(
                            ThresholdCompOp::Leq,
                            Vec::<(Parameter, Fraction)>::new(),
                            1,
                        ),
                    ),
                )),
                BooleanConnective::And,
                Box::new(LIAVariableConstraint::SingleVarConstraint(
                    SingleAtomConstraint::new(
                        Variable::new("var1"),
                        ThresholdConstraint::new(
                            ThresholdCompOp::Geq,
                            Vec::<(Parameter, Fraction)>::new(),
                            1,
                        ),
                    ),
                )),
            )],
            additional_vars_for_sums: HashMap::new(),
        };

        assert_eq!(lia_ta, expected_lia);
    }

    #[test]
    fn test_error_on_non_lia() {
        let violating_rule = RuleBuilder::new(1, Location::new("loc2"), Location::new("loc3"))
            .with_guard(
                BooleanVarConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(1)),
                ) & BooleanVarConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                    ComparisonOp::Eq,
                    Box::new(
                        IntegerExpression::Param(Parameter::new("n"))
                            * IntegerExpression::Atom(Variable::new("var2")),
                    ),
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
            .build();

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
            .with_initial_location_constraints(vec![
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
            ])
            .unwrap()
            .with_rules(vec![
                RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2"))
                    .with_actions(vec![
                        Action::new(
                            Variable::new("var1"),
                            IntegerExpression::Atom(Variable::new("var1")),
                        )
                        .unwrap(),
                    ])
                    .build(),
                violating_rule.clone(),
            ])
            .unwrap()
            .with_resilience_conditions(vec![ParameterConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::Atom(Parameter::new("f"))),
                    IntegerOp::Mul,
                    Box::new(IntegerExpression::Atom(Parameter::new("f"))),
                )),
            )])
            .unwrap()
            .build();
        let lia_ta = LIAThresholdAutomaton::try_from(ta.clone());
        assert!(lia_ta.is_err());

        let err = lia_ta.unwrap_err();
        assert!(matches!(
            err.clone(),
            LIATransformationError::GuardError(_, _, _)
        ));
        assert!(err.to_string().contains(&violating_rule.to_string()))
    }
}
