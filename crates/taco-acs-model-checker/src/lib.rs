//! Abstract Counter System Model Checker
//!
//! This crate implements a counter system based model checker as described
//! in the paper
//! ["Parameterized Verification of Round-based Distributed Algorithms via Extended Threshold Automata"](https://arxiv.org/abs/2406.19880).
//! This model checker will construct the explicit counter system (`ACS` in the
//! paper), starting from potential error states and checking whether an initial
//! state is reachable.
//! If a path is found, the SMT checker will be used to check whether the path
//! is spurious.
//!
//! Note that this model checker does not support "reachability" specifications,
//! i.e. specifications, that require a location to be not covered by any
//! process.

use core::fmt;
use std::{convert::Infallible, error};

use log::{info, warn};
use taco_interval_ta::IntervalThresholdAutomaton;
use taco_model_checker::{
    ModelChecker, ModelCheckerResult, TASpecOf,
    internal_spec::{ErrorSpec, ErrorTarget},
};
use taco_smt_encoder::SMTSolverBuilder;

use crate::{acs_threshold_automaton::ACSThresholdAutomaton, error_graph::ErrorGraph};

pub mod partial_ord;

pub mod error_graph;

pub mod acs_threshold_automaton;

/// Counter system based model checker
///
/// This crate implements a counter system based model checker as described
/// in the paper
/// ["Parameterized Verification of Round-based Distributed Algorithms via Extended Threshold Automata"](https://arxiv.org/abs/2406.19880).
/// This model checker will construct the explicit counter system (`ACS` in the
/// paper), starting from potential error states and checking whether an initial
/// state is reachable.
/// If a path is found, the SMT checker will be used to check whether the path
/// is spurious.
///
/// Note that this model checker does not support "reachability" specifications,
/// i.e. specifications, that require a location to be not covered by any
/// process.
#[derive(Debug, Clone)]
pub struct ACSModelChecker {
    /// Threshold automata and specifications to check
    ta_spec: TASpecOf<Self>,
    /// Properties that could not be translated
    unknown: Vec<String>,
    /// SMT solver builder used for spurious checks
    ctx: SMTSolverBuilder,
}

impl ModelChecker for ACSModelChecker {
    type ModelCheckerContext = SMTSolverBuilder;

    type ModelCheckerOptions = Option<()>;

    type SpecType = ErrorSpec;

    type ThresholdAutomatonType = IntervalThresholdAutomaton;

    type InitializationError = ACSModelCheckerInitializationError;

    type ModelCheckingError = Infallible;

    fn initialize(
        _mode: Self::ModelCheckerOptions,
        ta_spec: TASpecOf<Self>,
        unknown: Vec<String>,
        ctx: Self::ModelCheckerContext,
    ) -> Result<Self, Self::InitializationError> {
        if let Some((_, reach_spec, _)) = ta_spec
            .iter()
            .find(|(_, s, _)| s.contains_reachability_constraint())
        {
            return Err(ACSModelCheckerInitializationError::ReachabilitySpec(
                Box::new(reach_spec.clone()),
            ));
        }

        Ok(Self {
            ta_spec,
            unknown,
            ctx,
        })
    }

    fn verify(
        self,
        abort_on_violation: bool,
    ) -> Result<ModelCheckerResult, Self::ModelCheckingError> {
        let mut unsafe_properties = Vec::new();
        let mut unknown_properties = self.unknown;

        for (name, target, tas) in self.ta_spec {
            let ErrorTarget::Reach(spec) = target else {
                warn!("Property '{name}' ({target}) is not supported by the ACS model checker");
                unknown_properties.push(name);
                continue;
            };

            for ta in tas.into_iter().map(ACSThresholdAutomaton::new) {
                let error_graph = ErrorGraph::compute_error_graph(spec.clone(), ta);

                if error_graph.is_empty() {
                    info!(
                        "Error graph of property {} is empty, property is SAFE in this interval order.",
                        spec
                    );
                    continue;
                }

                let solver = self.ctx.new_solver();

                info!(
                    "Error graph of property {} is not empty, checking paths for spuriousness",
                    spec
                );
                let res = error_graph.check_for_non_spurious_counter_example(solver);

                match res {
                    ModelCheckerResult::SAFE => info!(
                        "Error graph of property {} is spurious, property is SAFE in this interval order.",
                        spec
                    ),
                    ModelCheckerResult::UNSAFE { violations, .. } => {
                        info!("Found counterexample to property {}", name);
                        unsafe_properties
                            .extend(violations.into_iter().map(|(_, p)| (name.clone(), p)));

                        if abort_on_violation {
                            return Ok(ModelCheckerResult::UNSAFE {
                                violations: unsafe_properties,
                                unknown: unknown_properties,
                            });
                        }
                    }
                    ModelCheckerResult::UNKNOWN(_) => {
                        info!(
                            "The model checker could not determine whether property {} is safe or unsafe",
                            spec
                        );
                        unknown_properties.push(name.clone());
                    }
                }
            }
        }

        if !unsafe_properties.is_empty() {
            return Ok(ModelCheckerResult::UNSAFE {
                violations: unsafe_properties,
                unknown: unknown_properties,
            });
        }
        if !unknown_properties.is_empty() {
            return Ok(ModelCheckerResult::UNKNOWN(unknown_properties));
        }

        Ok(ModelCheckerResult::SAFE)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum ACSModelCheckerInitializationError {
    ReachabilitySpec(Box<ErrorTarget>),
}

impl fmt::Display for ACSModelCheckerInitializationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ACSModelCheckerInitializationError::ReachabilitySpec(spec) => {
                write!(
                    f,
                    "The counter system model checker does not support reachability specifications, but property {} contains a reachability constraint",
                    spec
                )
            }
        }
    }
}

impl error::Error for ACSModelCheckerInitializationError {}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use taco_model_checker::{ModelChecker, ModelCheckerResult, ModelCheckerSetupError};
    use taco_parser::{ParseTAWithLTL, bymc::ByMCParser};
    use taco_smt_encoder::SMTSolverBuilderCfg;
    use taco_threshold_automaton::{
        expressions::{
            BooleanExpression, ComparisonOp, IntegerExpression, Location, Parameter, Variable,
        },
        general_threshold_automaton::{Action, UpdateExpression, builder::RuleBuilder},
        path::{Configuration, PathBuilder, Transition},
    };

    use crate::{ACSModelChecker, ACSModelCheckerInitializationError};

    #[test]
    fn test_full_model_checker_reach_location_three_rules_one_guard_self_loop() {
        let test_spec = "
            skel test_ta1 {
                shared var1, var2, var3;
                parameters n, f;
                
                assumptions (1) {
                    n > 3 * f;
                    n == 1;
                    f == 0;
                }

                locations (2) {
                    loc1 : [0];
                    loc2 : [1];
                    loc3 : [2];
                }

                inits (1) {
                    loc1 == n - f;
                    loc2 == 0;
                    loc3 == 0;
                    var1 == 0;
                    var2 == 0;
                    var3 == 0;
                }

                rules (4) {
                    0: loc1 -> loc1
                        when(true)
                        do {var1' == var1 + 1};
                    1: loc1 -> loc2
                        when(true)
                        do {};
                    2: loc2 -> loc3
                        when(var1 > 3 && var2 <= 0 && var1 <= 4)
                        do {};
                    
                }

                specifications (1) {
                    test1:
                        [](loc3 == 0)
                }
            }
            ";

        let (ta, spec) = ByMCParser::new().parse_ta_and_spec(test_spec).unwrap();

        let mc = ACSModelChecker::new(
            Some(SMTSolverBuilderCfg::new_z3()),
            None,
            Vec::new(),
            ta.clone(),
            spec.into_iter(),
        );
        let mc = mc.unwrap();
        let res = mc.verify(true).unwrap();

        let path = PathBuilder::new(ta.clone())
            .add_parameter_assignment(HashMap::from([
                (Parameter::new("n"), 1),
                (Parameter::new("f"), 0),
            ]))
            .unwrap()
            .add_configuration(Configuration::new(
                HashMap::from([
                    (Variable::new("var1"), 0),
                    (Variable::new("var2"), 0),
                    (Variable::new("var3"), 0),
                ]),
                HashMap::from([
                    (Location::new("loc1"), 1),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 0),
                ]),
            ))
            .unwrap()
            .add_transition(Transition::new(
                RuleBuilder::new(0, Location::new("loc1"), Location::new("loc1"))
                    .with_action(Action::new_with_update(
                        Variable::new("var1"),
                        UpdateExpression::Inc(1),
                    ))
                    .build(),
                1,
            ))
            .unwrap()
            .add_configuration(Configuration::new(
                HashMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 0),
                    (Variable::new("var3"), 0),
                ]),
                HashMap::from([
                    (Location::new("loc1"), 1),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 0),
                ]),
            ))
            .unwrap()
            .add_transition(Transition::new(
                RuleBuilder::new(0, Location::new("loc1"), Location::new("loc1"))
                    .with_action(Action::new_with_update(
                        Variable::new("var1"),
                        UpdateExpression::Inc(1),
                    ))
                    .build(),
                2,
            ))
            .unwrap()
            .add_configuration(Configuration::new(
                HashMap::from([
                    (Variable::new("var1"), 3),
                    (Variable::new("var2"), 0),
                    (Variable::new("var3"), 0),
                ]),
                HashMap::from([
                    (Location::new("loc1"), 1),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 0),
                ]),
            ))
            .unwrap()
            .add_transition(Transition::new(
                RuleBuilder::new(0, Location::new("loc1"), Location::new("loc1"))
                    .with_action(Action::new_with_update(
                        Variable::new("var1"),
                        UpdateExpression::Inc(1),
                    ))
                    .build(),
                1,
            ))
            .unwrap()
            .add_configuration(Configuration::new(
                HashMap::from([
                    (Variable::new("var1"), 4),
                    (Variable::new("var2"), 0),
                    (Variable::new("var3"), 0),
                ]),
                HashMap::from([
                    (Location::new("loc1"), 1),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 0),
                ]),
            ))
            .unwrap()
            .add_transition(Transition::new(
                RuleBuilder::new(1, Location::new("loc1"), Location::new("loc2")).build(),
                1,
            ))
            .unwrap()
            .add_configuration(Configuration::new(
                HashMap::from([
                    (Variable::new("var1"), 4),
                    (Variable::new("var2"), 0),
                    (Variable::new("var3"), 0),
                ]),
                HashMap::from([
                    (Location::new("loc1"), 0),
                    (Location::new("loc2"), 1),
                    (Location::new("loc3"), 0),
                ]),
            ))
            .unwrap()
            .add_transition(Transition::new(
                RuleBuilder::new(2, Location::new("loc2"), Location::new("loc3"))
                    .with_guard(
                        BooleanExpression::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                            ComparisonOp::Gt,
                            Box::new(IntegerExpression::Const(3)),
                        ) & BooleanExpression::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                            ComparisonOp::Leq,
                            Box::new(IntegerExpression::Const(0)),
                        ) & BooleanExpression::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                            ComparisonOp::Leq,
                            Box::new(IntegerExpression::Const(4)),
                        ),
                    )
                    .build(),
                1,
            ))
            .unwrap()
            .add_configuration(Configuration::new(
                HashMap::from([
                    (Variable::new("var1"), 4),
                    (Variable::new("var2"), 0),
                    (Variable::new("var3"), 0),
                ]),
                HashMap::from([
                    (Location::new("loc1"), 0),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 1),
                ]),
            ))
            .unwrap()
            .build()
            .unwrap();

        let res = match res {
            ModelCheckerResult::SAFE => {
                unreachable!("Expected UNSAFE result based on test specification")
            }
            ModelCheckerResult::UNSAFE { violations: v, .. } => {
                assert_eq!(v.len(), 1);
                *v[0].1.clone()
            }
            ModelCheckerResult::UNKNOWN(_) => todo!(),
        };

        assert_eq!(
            res,
            path.clone(),
            "Got:\n{}\n\nExpected:\n{}\n\n",
            res,
            path
        );
    }

    #[test]
    fn test_full_model_checker_reach_location_three_rules_one_guard_self_loop_with_var_constr() {
        let test_spec = "
            skel test_ta1 {
                shared var1, var2, var3;
                parameters n, f;
                
                assumptions (1) {
                    n > 3 * f;
                    n == 1;
                    f == 0;
                }

                locations (2) {
                    loc1 : [0];
                    loc2 : [1];
                    loc3 : [2];
                }

                inits (1) {
                    loc1 == n - f;
                    loc2 == 0;
                    loc3 == 0;
                    var1 == 0;
                    var2 == 0;
                    var3 == 0;
                }

                rules (4) {
                    0: loc1 -> loc1
                        when(true)
                        do {var1' == var1 + 1};
                    1: loc1 -> loc2
                        when(true)
                        do {};
                    2: loc2 -> loc3
                        when(var1 > 3 && var2 <= 0 && var1 < 6 )
                        do {};
                    
                }

                specifications (1) {
                    test1:
                        []((loc3 == 0) || (var1 < 5))
                }
            }
            ";

        let (ta, spec) = ByMCParser::new().parse_ta_and_spec(test_spec).unwrap();

        let mc = ACSModelChecker::new(
            Some(SMTSolverBuilderCfg::new_z3()),
            None,
            Vec::new(),
            ta.clone(),
            spec.into_iter(),
        );
        let mc = mc.unwrap();
        let res = mc.verify(true).unwrap();

        // Replicate interval ta for path builder

        let path = PathBuilder::new(ta.clone())
            .add_parameter_assignment(HashMap::from([
                (Parameter::new("n"), 1),
                (Parameter::new("f"), 0),
            ]))
            .unwrap()
            .add_configuration(Configuration::new(
                HashMap::from([
                    (Variable::new("var1"), 0),
                    (Variable::new("var2"), 0),
                    (Variable::new("var3"), 0),
                ]),
                HashMap::from([
                    (Location::new("loc1"), 1),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 0),
                ]),
            ))
            .unwrap()
            .add_transition(Transition::new(
                RuleBuilder::new(0, Location::new("loc1"), Location::new("loc1"))
                    .with_action(Action::new_with_update(
                        Variable::new("var1"),
                        UpdateExpression::Inc(1),
                    ))
                    .build(),
                5,
            ))
            .unwrap()
            .add_configuration(Configuration::new(
                HashMap::from([
                    (Variable::new("var1"), 5),
                    (Variable::new("var2"), 0),
                    (Variable::new("var3"), 0),
                ]),
                HashMap::from([
                    (Location::new("loc1"), 1),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 0),
                ]),
            ))
            .unwrap()
            .add_transition(Transition::new(
                RuleBuilder::new(1, Location::new("loc1"), Location::new("loc2")).build(),
                1,
            ))
            .unwrap()
            .add_configuration(Configuration::new(
                HashMap::from([
                    (Variable::new("var1"), 5),
                    (Variable::new("var2"), 0),
                    (Variable::new("var3"), 0),
                ]),
                HashMap::from([
                    (Location::new("loc1"), 0),
                    (Location::new("loc2"), 1),
                    (Location::new("loc3"), 0),
                ]),
            ))
            .unwrap()
            .add_transition(Transition::new(
                RuleBuilder::new(2, Location::new("loc2"), Location::new("loc3"))
                    .with_guard(
                        BooleanExpression::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                            ComparisonOp::Gt,
                            Box::new(IntegerExpression::Const(3)),
                        ) & BooleanExpression::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                            ComparisonOp::Leq,
                            Box::new(IntegerExpression::Const(0)),
                        ) & BooleanExpression::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                            ComparisonOp::Lt,
                            Box::new(IntegerExpression::Const(6)),
                        ),
                    )
                    .build(),
                1,
            ))
            .unwrap()
            .add_configuration(Configuration::new(
                HashMap::from([
                    (Variable::new("var1"), 5),
                    (Variable::new("var2"), 0),
                    (Variable::new("var3"), 0),
                ]),
                HashMap::from([
                    (Location::new("loc1"), 0),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 1),
                ]),
            ))
            .unwrap()
            .build()
            .unwrap();

        let res = match res {
            ModelCheckerResult::SAFE => {
                unreachable!("Expected UNSAFE result based on test specification")
            }
            ModelCheckerResult::UNSAFE { violations: v, .. } => {
                assert_eq!(v.len(), 1);
                *v[0].1.clone()
            }
            ModelCheckerResult::UNKNOWN(_) => todo!(),
        };

        assert_eq!(
            res,
            path.clone(),
            "Got:\n{}\n\nExpected:\n{}\n\n",
            res,
            path
        );
    }

    #[test]
    fn test_err_on_reach_spec() {
        let test_spec = "
            skel test_ta1 {
                shared var1, var2, var3;
                parameters n, f;
                
                assumptions (1) {
                    n > 3 * f;
                    n == 1;
                    f == 0;
                }

                locations (2) {
                    loc1 : [0];
                    loc2 : [1];
                    loc3 : [2];
                }

                inits (1) {
                    loc1 == n - f;
                    loc2 == 0;
                    loc3 == 0;
                    var1 == 0;
                    var2 == 0;
                    var3 == 0;
                }

                rules (4) {
                    0: loc1 -> loc1
                        when(true)
                        do {var1' == var1 + 1};
                    1: loc1 -> loc2
                        when(true)
                        do {};
                    2: loc2 -> loc3
                        when(var1 > 3 && var2 <= 0 && var1 <= 4)
                        do {};
                    
                }

                specifications (1) {
                    test1:
                        [](loc3 == 0 && loc2 != 0)
                }
            }
            ";

        let (ta, spec) = ByMCParser::new().parse_ta_and_spec(test_spec).unwrap();

        let mc = ACSModelChecker::new(
            Some(SMTSolverBuilderCfg::new_z3()),
            None,
            Vec::new(),
            ta.clone(),
            spec.into_iter(),
        );

        assert!(mc.is_err());

        assert!(matches!(
            mc.unwrap_err(),
            ModelCheckerSetupError::ErrorInitializingModelChecker(
                ACSModelCheckerInitializationError::ReachabilitySpec(_)
            )
        ));
    }

    /// Check that results are reported per property name, and that
    /// properties the model checker cannot decide are reported as unknown
    #[test]
    fn test_result_reporting_per_property() {
        let run = |specs: &str| {
            let (ta, spec) = ByMCParser::new()
                .parse_ta_and_spec(&format!(
                    "
            skel test_ta1 {{
                shared var1;
                parameters n, f;

                assumptions (1) {{
                    n > 3 * f;
                    n == 1;
                }}

                locations (2) {{
                    loc1 : [0];
                    loc2 : [1];
                    loc3 : [2];
                }}

                inits (1) {{
                    loc1 == n - f;
                    loc2 == 0;
                    loc3 == 0;
                    var1 == 0;
                }}

                rules (4) {{
                    0: loc1 -> loc2
                        when(true)
                        do {{}};
                }}

                specifications (1) {{
                    {specs}
                }}
            }}
                    "
                ))
                .unwrap();

            let mc = ACSModelChecker::new(
                Some(SMTSolverBuilderCfg::new_z3()),
                None,
                Vec::new(),
                ta,
                spec.expressions().iter().cloned(),
            );
            mc.expect("Failed to create model checker")
                .verify(false)
                .expect("Failed to model check")
        };

        let res = run("
            holds: [](loc3 == 0);
            reach_violated: [](loc2 == 0);
            init_violated: loc1 == 0;
            untranslatable: [](<>(loc1 == 0 || [](loc2 == 0)));
        ");
        let ModelCheckerResult::UNSAFE {
            violations,
            unknown,
        } = res
        else {
            panic!("Expected UNSAFE, got {res:?}");
        };
        assert_eq!(unknown, vec!["untranslatable"]);
        let mut names = violations
            .iter()
            .map(|(n, _)| n.as_str())
            .collect::<Vec<_>>();
        names.sort();
        assert_eq!(names, vec!["init_violated", "reach_violated"]);

        let res = run("
            holds: [](loc3 == 0);
            liveness: <>(loc2 != 0);
            untranslatable: [](<>(loc1 == 0 || [](loc2 == 0)));
        ");
        let ModelCheckerResult::UNKNOWN(mut unknown) = res else {
            panic!("Expected UNKNOWN, got {res:?}");
        };
        unknown.sort();
        assert_eq!(unknown, vec!["liveness", "untranslatable"]);
    }
}
