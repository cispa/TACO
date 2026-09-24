//! Builder for interval threshold automaton
//!
//! This module provides a builder for generating interval threshold automata
//! from linear integer arithmetic threshold automata. In the process, the
//! builder also generates all possible interval orders for the given threshold
//! automaton.

use taco_smt_encoder::SMTSolverBuilder;
use taco_threshold_automaton::{
    RuleDefinition, ThresholdAutomaton,
    lia_threshold_automaton::{LIAThresholdAutomaton, LIAVariableConstraint},
};

use crate::{
    IntervalConstraint, IntervalTARule, IntervalTATransformationError, IntervalThresholdAutomaton,
    builder::static_interval_order::{StaticIntervalOrder, StaticIntervalOrderBuilder},
    interval::{IntervalBoundary, IntervalOrder},
};

use log::error;

pub mod static_interval_order;

/// Builder for generating interval threshold automata
///
/// This builder takes a linear integer arithmetic threshold automaton and
/// derives all valid interval threshold automata.
///
/// An interval threshold automaton is a threshold automaton where the guards
/// are abstracted to intervals and the order of the intervals is defined.
///
/// The builder generates all possible interval orders for the given threshold
/// linear integer arithmetic automaton, and for each interval order, it
/// generates the corresponding interval threshold automaton.
pub struct IntervalTABuilder {
    /// Underlying threshold automaton
    lia_ta: LIAThresholdAutomaton,
    /// Solver builder for generating the interval orders
    solver_builder: SMTSolverBuilder,
    /// Additional variable constraints derived from the target specification
    target_constr: Vec<LIAVariableConstraint>,
}

impl IntervalTABuilder {
    /// Create a new interval threshold automaton builder from a linear integer
    /// arithmetic threshold automaton
    ///
    /// The solver builder is used to generate the interval orders.
    pub fn new(
        lia_ta: LIAThresholdAutomaton,
        solver_builder: SMTSolverBuilder,
        target_constr: Vec<LIAVariableConstraint>,
    ) -> Self {
        Self {
            lia_ta,
            solver_builder,
            target_constr,
        }
    }

    /// Generate all possible orders on the intervals and derive the interval
    /// automaton for every possible order
    pub fn build(
        self,
    ) -> Result<impl Iterator<Item = IntervalThresholdAutomaton>, IntervalTATransformationError>
    {
        let order_builder = StaticIntervalOrderBuilder::new(&self.lia_ta, self.solver_builder);

        let order_builder =
            self.lia_ta
                .initial_variable_constraints()
                .try_fold(order_builder, |acc, constr| {
                    Self::discover_interval_boundaries_in_lia_variable_constraint(constr, acc)
                        .ok_or_else(|| {
                            IntervalTATransformationError::ComparisonGuardFoundInitialVariableConstraint(Box::new(constr.clone()))
                        })
                })?;

        let order_builder = self.lia_ta.rules().try_fold(order_builder, |acc, rule| {
            Self::discover_interval_boundaries_in_lia_variable_constraint(rule.guard(), acc)
                .ok_or_else(|| {
                    IntervalTATransformationError::ComparisonGuardFoundRule(Box::new(rule.clone()))
                })
        })?;

        let order_builder =
            self.target_constr
                .into_iter()
                .try_fold(order_builder, |acc, constr| {
                    Self::discover_interval_boundaries_in_lia_variable_constraint(&constr, acc)
                        .ok_or_else(|| {
                            IntervalTATransformationError::ComparisonGuardFoundVariableTarget(
                                Box::new(constr.clone()),
                            )
                        })
                })?;

        let orders = order_builder.build();

        Ok(orders.into_iter().map(move |order| {
            Self::derive_interval_threshold_automaton(self.lia_ta.clone(), order)
        }))
    }

    /// Given a fixed order, derive the abstract threshold automaton
    fn derive_interval_threshold_automaton(
        lia_ta: LIAThresholdAutomaton,
        interval_order: StaticIntervalOrder,
    ) -> IntervalThresholdAutomaton {
        let rules = lia_ta
            .rules()
            .map(|rule| IntervalTARule::from_lia_rule(rule, &interval_order))
            .collect::<Vec<_>>();

        let initial_variable_constraints = lia_ta
            .initial_variable_constraints()
            .map(|constr| {
                IntervalConstraint::from_lia_constr(constr, &interval_order)
                    .expect("Failed to derive interval constraint from initial constraint")
            })
            .collect();

        let order_expr = interval_order.order_to_boolean_expr();
        IntervalThresholdAutomaton {
            lia_ta,
            rules,
            initial_variable_constraints,
            order: interval_order,
            order_expr,
        }
    }

    /// Extract variable intervals from a rule guard of the threshold automaton
    ///
    /// Returns None if a comparison guard has been discovered
    fn discover_interval_boundaries_in_lia_variable_constraint(
        guard: &LIAVariableConstraint,
        order_builder: StaticIntervalOrderBuilder,
    ) -> Option<StaticIntervalOrderBuilder> {
        match guard {
            LIAVariableConstraint::True | LIAVariableConstraint::False => Some(order_builder),
            LIAVariableConstraint::ComparisonConstraint(_guard) => {
                error!("Comparison Guard found. Guard {guard}");
                None
            }
            LIAVariableConstraint::BinaryGuard(lhs, _op, rhs) => {
                // Recursively extract interval boundaries from the left and right hand side
                let order_builder = Self::discover_interval_boundaries_in_lia_variable_constraint(
                    lhs,
                    order_builder,
                )?;
                Self::discover_interval_boundaries_in_lia_variable_constraint(rhs, order_builder)
            }
            LIAVariableConstraint::SingleVarConstraint(thr_guard) => {
                let interval_boundary = IntervalBoundary::from_threshold_constraint(
                    thr_guard.get_threshold_constraint(),
                );

                // We need to add the exact interval into the order to correctly
                // determine when constraints are satisfied
                let exact_required = thr_guard
                    .get_threshold_constraint()
                    .get_op()
                    .needs_exact_interval();

                Some(order_builder.add_single_variable_interval(
                    thr_guard.get_atom(),
                    &interval_boundary,
                    exact_required,
                ))
            }
            LIAVariableConstraint::SumVarConstraint(thr_guard) => {
                let interval_boundary = IntervalBoundary::from_threshold_constraint(
                    thr_guard.get_threshold_constraint(),
                );

                let exact_required = thr_guard
                    .get_threshold_constraint()
                    .get_op()
                    .needs_exact_interval();

                Some(order_builder.add_multi_variable_interval(
                    thr_guard.get_atoms(),
                    &interval_boundary,
                    exact_required,
                ))
            }
        }
    }
}

#[cfg(test)]
mod test {
    use taco_smt_encoder::SMTSolverBuilder;
    use taco_threshold_automaton::{
        expressions::{
            BooleanExpression, ComparisonOp, IntegerExpression, Location, Parameter, Variable,
        },
        general_threshold_automaton::{
            Action,
            builder::{GeneralThresholdAutomatonBuilder, RuleBuilder},
        },
        lia_threshold_automaton::{LIARule, LIAThresholdAutomaton, LIAVariableConstraint},
    };

    use crate::{IntervalTATransformationError, builder::IntervalTABuilder};

    #[test]
    fn test_builder_for_lia_ta_err_on_comparison_constr_target() {
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
            Box::new(IntegerExpression::Atom(Variable::new("y"))),
        ))
            .try_into()
            .unwrap();

        let interval_tas = IntervalTABuilder::new(
            lia_ta,
            SMTSolverBuilder::default(),
            vec![lia_constr.clone()],
        )
        .build();

        assert!(interval_tas.is_err());
        if let Err(e) = interval_tas {
            assert_eq!(
                e,
                IntervalTATransformationError::ComparisonGuardFoundVariableTarget(Box::new(
                    lia_constr.clone()
                ))
            );
        }
    }

    #[test]
    fn test_builder_for_lia_ta_err_on_comparison_constr_init_loc() {
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
            .with_initial_variable_constraint(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("x"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Atom(Variable::new("y"))),
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

        let interval_tas =
            IntervalTABuilder::new(lia_ta, SMTSolverBuilder::default(), vec![]).build();

        let lia_constr: LIAVariableConstraint = (&BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Variable::new("x"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Atom(Variable::new("y"))),
        ))
            .try_into()
            .unwrap();

        assert!(interval_tas.is_err());
        if let Err(e) = interval_tas {
            assert_eq!(
                e,
                IntervalTATransformationError::ComparisonGuardFoundInitialVariableConstraint(
                    Box::new(lia_constr.clone())
                )
            );
        }
    }

    #[test]
    fn test_builder_for_lia_ta_err_on_comparison_rule() {
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
                        Box::new(IntegerExpression::Atom(Variable::new("x"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Atom(Variable::new("y"))),
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

        let interval_tas =
            IntervalTABuilder::new(lia_ta, SMTSolverBuilder::default(), vec![]).build();

        let rule = LIARule::try_from(
            RuleBuilder::new(0, Location::new("l1"), Location::new("l2"))
                .with_guard(BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("x"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Atom(Variable::new("y"))),
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
        .unwrap();

        assert!(interval_tas.is_err());
        if let Err(e) = interval_tas {
            assert_eq!(
                e,
                IntervalTATransformationError::ComparisonGuardFoundRule(Box::new(rule))
            );
        }
    }
}
