//! This module implements the encoding of query on threshold automata into SMT
//! expressions. The algorithm is based on the encoding described in the paper
//! ["Complexity of Verification and Synthesis of Threshold Automata"](https://arxiv.org/abs/2002.08507)
//! by A. R. Balasubramanian, Javier Esparza, Marijana Lazic.
//!
//! The paper does not provide a complete encoding of the threshold automata,
//! instead many implementation details are not provided. As we were not
//! provided with the source code (nor an executable) of the implementation used
//! in the paper, we  had to make some assumptions about the implementation
//! details.
//!
//! We will explicitly mark functions that are not directly described in the
//! paper.

use core::fmt;
use std::{collections::HashMap, ops::Deref, rc::Rc};

use log::{debug, info};
use taco_display_utils::join_iterator;

use taco_model_checker::internal_spec::upwards_closed_set::UpwardsClosedSet;
use taco_smt_encoder::{
    SMTExpr, SMTSolver, SMTSolverBuilder, SMTSolverContext,
    expression_encoding::{
        DeclaresVariable, EncodeToSMT,
        config_ctx::ConfigCtx,
        ctx_mgr::SMTConfigMgr,
        step_ctx::LazyStepContext,
        ta_encoding::{encode_initial_constraints, encode_resilience_condition},
    },
};

use taco_threshold_automaton::{
    ThresholdAutomaton,
    expressions::Parameter,
    general_threshold_automaton::GeneralThresholdAutomaton,
    lia_threshold_automaton::{
        LIAThresholdAutomaton, LIATransformationError, LIAVariableConstraint,
    },
    path::Path,
};

// Type alias for the concrete step context used for this model checker
type StepCtx = LazyStepContext<GeneralThresholdAutomaton, ConfigCtx>;

#[derive(Debug)]
pub enum ContextMgrError {
    /// Threshold automaton is not a LIA threshold automaton
    LIATransformationError(LIATransformationError),
}

impl fmt::Display for ContextMgrError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ContextMgrError::LIATransformationError(e) => {
                write!(f, "Automaton is not using linear arithmetic: {e}")
            }
        }
    }
}

impl std::error::Error for ContextMgrError {}

pub struct EContextMgr {
    solver: SMTSolver,
    ta: Rc<GeneralThresholdAutomaton>,
    k: usize,
    ctx_mgr: SMTConfigMgr<StepCtx, ConfigCtx>,
}

impl fmt::Debug for EContextMgr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ContextMgr {{ ta: {}, k: {} }}", self.ta, self.k)
    }
}

impl EContextMgr {
    pub fn new(
        ta: GeneralThresholdAutomaton,
        target_constr: &[&LIAVariableConstraint],
        smt_builder: &SMTSolverBuilder,
    ) -> Result<Self, ContextMgrError> {
        let mut solver = smt_builder.new_solver();

        let ta = Rc::new(ta);

        let params: Rc<HashMap<Parameter, SMTExpr>> = Rc::new(
            ta.parameters()
                .map(|p| {
                    let param = p
                        .declare_variable(&mut solver, 0)
                        .expect("Failed to declare parameter");

                    solver
                        .assert(solver.gte(param, solver.numeral(0)))
                        .expect("Failed to assert parameter >= 0");

                    (p.clone(), param)
                })
                .collect(),
        );

        let k = Self::compute_k_for_ta(&ta, target_constr)?;
        info!(
            "Determined number of steady steps k for threshold automaton '{}' to be {k}",
            ta.name()
        );

        let mut ctx_mgr = SMTConfigMgr::new(params.clone());

        let mut prev_primed_config = None;

        for i in 0..k {
            let config_index = 2 * i;
            let config_primed_index = 2 * i + 1;

            // Create config context σ_i
            let config = Rc::new(ConfigCtx::new(
                &mut solver,
                ta.as_ref(),
                params.clone(),
                config_index,
            ));
            ctx_mgr.push_cfg(config.clone());

            // Create config context σ'_i
            let config_primed = Rc::new(ConfigCtx::new(
                &mut solver,
                ta.as_ref(),
                params.clone(),
                config_primed_index,
            ));
            ctx_mgr.push_cfg_primed(config_primed.clone());

            // Create step context for ϕ_steady (σ_i,σ'_i)
            let steady_step = LazyStepContext::new(
                ta.rules().cloned(),
                ta.clone(),
                config.clone(),
                config_primed.clone(),
                config_index,
                &mut solver,
            );
            ctx_mgr.push_steady(steady_step);

            // Create step context ϕ_step (σ'_{i-1}, σ_i)
            if let Some(prev_primed_config) = prev_primed_config {
                let step_step = LazyStepContext::new(
                    ta.rules().cloned(),
                    ta.clone(),
                    prev_primed_config,
                    config,
                    2 * (i - 1) + 1,
                    &mut solver,
                );

                ctx_mgr.push_step(step_step);
            }

            prev_primed_config = Some(config_primed.clone());
        }

        Ok(Self {
            solver,
            ta,
            k,
            ctx_mgr,
        })
    }

    /// Check whether the upwards closed set `spec` is reachable
    ///
    /// If the set is not reachable `None` is returned. Otherwise an error path is returned
    pub fn check_spec(mut self, spec: &UpwardsClosedSet) -> Option<Path> {
        self.encode_phi_reach(spec);

        debug!("Start check of ϕ_{{reach}}");
        let res = self
            .solver
            .assert_and_check_expr(self.solver.true_())
            .expect("Failed to check the encoding of the threshold automaton");
        debug!("SMT solver successfully checked ϕ_{{reach}} !");

        if !res.is_sat() {
            return None;
        }

        let err_path =
            self.ctx_mgr
                .extract_error_path(res, &mut self.solver, self.ta.deref().clone());
        Some(err_path)
    }

    /// Compute the number K for the threshold automaton
    ///
    /// In the paper, the number of guards is simply given as the size of the
    /// set of guards ϕ plus one, i.e. K = |ϕ| + 1.
    ///
    /// However, this assumes that all guards are in their strict upper and
    /// lower guard form. Therefore we need to convert the threshold automaton
    /// first into a `LIAThresholdAutomaton` and then compute the number K.
    ///
    fn compute_k_for_ta(
        ta: &GeneralThresholdAutomaton,
        target_constr: &[&LIAVariableConstraint],
    ) -> Result<usize, ContextMgrError> {
        //
        let lia_ta: LIAThresholdAutomaton = ta
            .clone()
            .try_into()
            .map_err(ContextMgrError::LIATransformationError)?;

        let mut s_guards = lia_ta.get_single_var_constraints_rules();

        // Add additional guards potentially arising from the target constraint
        s_guards.extend(
            target_constr
                .iter()
                .flat_map(|c| c.get_single_var_constraints()),
        );

        debug!(
            "Single variable guards: {}",
            join_iterator(s_guards.iter(), ", ")
        );
        let n_single_var_guards = s_guards.iter().fold(0, |mut acc, guard| {
            debug_assert!(guard.is_lower_guard() || guard.is_upper_guard());

            if guard.is_lower_guard() {
                acc += 1;
            }

            if guard.is_upper_guard() {
                acc += 1;
            }

            acc
        });

        let m_guards = lia_ta.get_sum_var_constraints();
        debug!(
            "Multi variable guards: {}",
            join_iterator(m_guards.iter(), ", ")
        );
        let n_multi_var_guards = m_guards.into_iter().fold(0, |mut acc, guard| {
            debug_assert!(guard.is_lower_guard() || guard.is_upper_guard());

            if guard.is_lower_guard() {
                acc += 1;
            }

            if guard.is_upper_guard() {
                acc += 1;
            }

            acc
        });

        debug_assert!(lia_ta.get_comparison_guards().is_empty());

        Ok(n_single_var_guards + n_multi_var_guards + 1)
    }

    /// Encodes the ϕ_{reach} of the threshold automaton
    fn encode_phi_reach(&mut self, spec: &UpwardsClosedSet) {
        // RC(p)
        let rc = encode_resilience_condition(
            self.ta.as_ref(),
            &self.solver,
            self.ctx_mgr.params().deref(),
        );
        self.solver
            .assert(rc)
            .expect("Failed to assert resilience condition");

        // σ = σ_0
        let init_config = self
            .ctx_mgr
            .configs()
            .next()
            .expect("No initial configuration found");
        let init_constraints =
            encode_initial_constraints(self.ta.as_ref(), &self.solver, init_config.as_ref());

        self.solver
            .assert(init_constraints)
            .expect("Failed to assert initial constraints");

        debug!("Finished encoding initial constraints");

        // σ' = σ_K
        let goal_constraints = self.encode_final_error_condition(spec);
        self.solver
            .assert(goal_constraints)
            .expect("Failed to assert goal constraints");

        // ∧_{0 ≤ i ≤ K} ϕ_{steady}(σ_i, σ_i')
        self.ctx_mgr.steady().for_each(|step| {
            let steady = step.encode_phi_steady(&self.solver);
            self.solver
                .assert(steady)
                .expect("Failed to assert steady step")
        });

        // ∧_{0 ≤ i ≤ K - 1} ϕ_{step}(σ_i', σ_{i+1})
        self.ctx_mgr.step().for_each(|step| {
            let step = step.encode_phi_step(&self.solver);
            self.solver
                .assert(step)
                .expect("Failed to assert step step")
        });

        info!(
            "Finished SMT encoding ϕ_{{reach}} for property '{}', start checking in SMT solver",
            spec
        );
    }

    /// Encodes the goal condition of the threshold automaton into an SMT
    fn encode_final_error_condition(&self, spec: &UpwardsClosedSet) -> SMTExpr {
        spec.encode_to_smt_with_ctx(
            &self.solver,
            self.ctx_mgr.configs_primed().last().unwrap().as_ref(),
        ) // k will always be greater than 1, therefore there should at least be one configuration
        .expect("Failed to encode the error state condition of the specification")
    }
}

#[cfg(test)]
mod tests {

    use std::collections::HashMap;

    use taco_model_checker::internal_spec::upwards_closed_set::UpwardsClosedSet;
    use taco_parser::{ParseTA, bymc::ByMCParser};
    use taco_smt_encoder::SMTSolverBuilder;
    use taco_threshold_automaton::{
        expressions::{
            BooleanConnective, BooleanExpression, ComparisonOp, IntegerExpression, Location,
            Parameter, Variable,
        },
        general_threshold_automaton::{
            Action, UpdateExpression,
            builder::{GeneralThresholdAutomatonBuilder, RuleBuilder},
        },
        path::{Configuration, PathBuilder, Transition},
    };

    use super::EContextMgr;

    // These tests rely on the bymc parser, since constructing complicated
    // threshold automata by hand is too error prone

    #[test]
    fn test_compute_k_no_guards() {
        let ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .initialize()
            .build();
        assert_eq!(EContextMgr::compute_k_for_ta(&ta, &[]).unwrap(), 1);
    }

    #[test]
    fn test_compute_k_only_lower_guards() {
        let test_spec = "
            skel test_ta1 {
                shared var1, var2, var3;
                parameters n, t, f;
                
                assumptions (1) {
                    n > 3 * f;
                }

                locations (2) {
                    loc1 : [0];
                    loc2 : [1];
                    loc3 : [2];
                }

                inits (1) {
                    loc1 == n - f  || loc2 == 0;
                    var1 == 0;
                    var2 == 0;
                    var3 == 0;
                }

                rules (4) {
                    0: loc1 -> loc2
                        when(true)
                        do {};
                    1: loc2 -> loc3
                        when( var1 < 1 && var2 <= n)
                        do { reset(var3); var1' == var1 + 1  };
                    2: loc2 -> loc3
                        when( var1 < 1)
                        do { reset(var3); var1' == var1 + 1  };
                    3: loc2 -> loc3
                        when( var1 < 3 || 2 * var1 < 6)
                        do { reset(var3); var1' == var1 + 1  };
                    4: loc2 -> loc3
                        when( var1 < 3 || var2 <=n )
                        do { reset(var3); var1' == var1 + 1  };
                    5: loc3 -> loc2
                        when ( var1 + var2 <= n + 1 + 5 - 3 - 2)
                        do { };
                    6: loc3 -> loc2
                        when ( var2 + var1 <= n + 1 + 5 - 3 - 2 - 1 + 1 )
                        do { };
                    7: loc3 -> loc2 
                        when ( var2 + var1 <= n + 1 ||  var2 + var1 <= 101 -100 + n) 
                        do { };
                }

                specifications (1) {
                }
            }
            ";

        let ta = ByMCParser::new().parse_ta(test_spec).unwrap();
        // var2 < n, var1 < 1, var1 < 3, var2 + var1 <= n + 1
        assert_eq!(EContextMgr::compute_k_for_ta(&ta, &[]).unwrap(), 5);
    }

    #[test]
    fn compute_k_upper_guards() {
        let test_spec = "
            skel test_ta1 {
                shared var1, var2, var3;
                parameters n, t, f;
                
                assumptions (1) {
                    n > 3 * f;
                }

                locations (2) {
                    loc1 : [0];
                    loc2 : [1];
                    loc3 : [2];
                }

                inits (1) {
                    loc1 == n - f  || loc2 == 0;
                    var1 == 0;
                    var2 == 0;
                    var3 == 0;
                }

                rules (4) {
                    0: loc1 -> loc2
                        when(true)
                        do {};
                    1: loc2 -> loc3
                        when( var1 > 1 && var2 >= n)
                        do { reset(var3); var1' == var1 + 1  };
                    2: loc2 -> loc3
                        when( var1 >= 1)
                        do { reset(var3); var1' == var1 + 1  };
                    3: loc2 -> loc3
                        when( var1 > 1)
                        do { reset(var3); var1' == var1 + 1  };
                    4: loc2 -> loc3
                        when( var1 > 3 || var2 >= n )
                        do { reset(var3); var1' == var1 + 1  };
                    5: loc3 -> loc2
                        when ( var2 + var1 > n + 1 + 5 - 3 - 2)
                        do { };
                    6: loc3 -> loc2
                        when ( var2 + var1 > n + 1 + 5 - 3 - 2 - 1 + 1  ||  var1 + var2  > 101 -100 + n)
                        do { };
                    7: loc3 -> loc2 
                        when ( var2 + var1 > n + 1) 
                        do { };
                }

                specifications (1) {
                }
            }
            ";

        let ta = ByMCParser::new().parse_ta(test_spec).unwrap();
        // var2 >= n, var1 >= 1, var1 > 1, var1 > 3, var1 + var2 > n + 1
        assert_eq!(EContextMgr::compute_k_for_ta(&ta, &[]).unwrap(), 6);
    }

    #[test]
    fn test_compute_k_with_additional_var_constr_increases_k() {
        let test_spec = "
            skel test_ta1 {
                shared var1, var2, var3;
                parameters n, t, f;
                
                assumptions (1) {
                    n > 3 * f;
                }

                locations (2) {
                    loc1 : [0];
                    loc2 : [1];
                    loc3 : [2];
                }

                inits (1) {
                    loc1 == n - f  || loc2 == 0;
                    var1 == 0;
                    var2 == 0;
                    var3 == 0;
                }

                rules (4) {
                    0: loc1 -> loc2
                        when(true)
                        do {};
                    1: loc2 -> loc3
                        when( var1 < 1 && var2 <= n)
                        do { reset(var3); var1' == var1 + 1  };
                    2: loc2 -> loc3
                        when( var1 < 1)
                        do { reset(var3); var1' == var1 + 1  };
                    3: loc2 -> loc3
                        when( var1 < 3 || 2 * var1 < 6)
                        do { reset(var3); var1' == var1 + 1  };
                    4: loc2 -> loc3
                        when( var1 < 3 || var2 <=n )
                        do { reset(var3); var1' == var1 + 1  };
                    5: loc3 -> loc2
                        when ( var1 + var2 <= n + 1 + 5 - 3 - 2)
                        do { };
                    6: loc3 -> loc2
                        when ( var2 + var1 <= n + 1 + 5 - 3 - 2 - 1 + 1 )
                        do { };
                    7: loc3 -> loc2 
                        when ( var2 + var1 <= n + 1 ||  var2 + var1 <= 101 -100 + n) 
                        do { };
                }

                specifications (1) {
                }
            }
            ";

        let ta = ByMCParser::new().parse_ta(test_spec).unwrap();
        let lia_constr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Variable::new("var1"))),
            ComparisonOp::Lt,
            Box::new(IntegerExpression::Const(4)),
        )
        .try_into()
        .unwrap();
        // var2 < n, var1 < 1, var1 < 3, var1 < 4, var2 + var1 <= n + 1
        assert_eq!(
            EContextMgr::compute_k_for_ta(&ta, &[&lia_constr]).unwrap(),
            6
        );
    }

    #[test]
    fn test_compute_k_with_additional_var_constr_already_in_guard() {
        let test_spec = "
            skel test_ta1 {
                shared var1, var2, var3;
                parameters n, t, f;
                
                assumptions (1) {
                    n > 3 * f;
                }

                locations (2) {
                    loc1 : [0];
                    loc2 : [1];
                    loc3 : [2];
                }

                inits (1) {
                    loc1 == n - f  || loc2 == 0;
                    var1 == 0;
                    var2 == 0;
                    var3 == 0;
                }

                rules (4) {
                    0: loc1 -> loc2
                        when(true)
                        do {};
                    1: loc2 -> loc3
                        when( var1 < 1 && var2 <= n)
                        do { reset(var3); var1' == var1 + 1  };
                    2: loc2 -> loc3
                        when( var1 < 1)
                        do { reset(var3); var1' == var1 + 1  };
                    3: loc2 -> loc3
                        when( var1 < 3 || 2 * var1 < 6)
                        do { reset(var3); var1' == var1 + 1  };
                    4: loc2 -> loc3
                        when( var1 < 3 || var2 <=n )
                        do { reset(var3); var1' == var1 + 1  };
                    5: loc3 -> loc2
                        when ( var1 + var2 <= n + 1 + 5 - 3 - 2)
                        do { };
                    6: loc3 -> loc2
                        when ( var2 + var1 <= n + 1 + 5 - 3 - 2 - 1 + 1 )
                        do { };
                    7: loc3 -> loc2 
                        when ( var2 + var1 <= n + 1 ||  var2 + var1 <= 101 -100 + n) 
                        do { };
                }

                specifications (1) {
                }
            }
            ";

        let ta = ByMCParser::new().parse_ta(test_spec).unwrap();
        let lia_constr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Variable::new("var1"))),
            ComparisonOp::Lt,
            Box::new(IntegerExpression::Const(3)),
        )
        .try_into()
        .unwrap();
        // var2 < n, var1 < 1, var1 < 3, var1 < 4, var2 + var1 <= n + 1
        assert_eq!(
            EContextMgr::compute_k_for_ta(&ta, &[&lia_constr]).unwrap(),
            5
        );
    }

    #[test]
    fn test_lower_and_upper_guards() {
        // lower and upper guard
        let test_spec = "
            skel test_ta1 {
                shared var1, var2, var3;
                parameters n, t, f;
                
                assumptions (1) {
                    n > 3 * f;
                }

                locations (2) {
                    loc1 : [0];
                    loc2 : [1];
                    loc3 : [2];
                }

                inits (1) {
                    loc1 == n - f  || loc2 == 0;
                    var1 == 0;
                    var2 == 0;
                    var3 == 0;
                }

                rules (4) {
                    0: loc1 -> loc2
                        when(true)
                        do {};
                    1: loc2 -> loc3
                        when( var1 == 1 && var2 != n)
                        do { reset(var3); var1' == var1 + 1  };
                }

                specifications (1) {
                }
            }
            ";

        let ta = ByMCParser::new().parse_ta(test_spec).unwrap();
        // var2 == n, var1 == 1
        assert_eq!(EContextMgr::compute_k_for_ta(&ta, &[]).unwrap(), 5);
    }

    #[test]
    fn test_spec_reach_initial_location() {
        let test_spec = "
            skel test_ta1 {
                shared var1, var2, var3;
                parameters n, f;
                
                assumptions (1) {
                    n > 3 * f;
                    n == 1;
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
                    0: loc1 -> loc2
                        when(true)
                        do {};
                }

                specifications (1) {
                    test1:
                        [](loc1 == 0)
                }
            }
            ";

        let ta = ByMCParser::new().parse_ta(test_spec).unwrap();

        let ctx_mgr = EContextMgr::new(ta.clone(), &[], &SMTSolverBuilder::default())
            .expect("Failed to create context manager");
        let spec = UpwardsClosedSet::new_cover([Location::new("loc1")]);

        let path = PathBuilder::new(ta)
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
            .build()
            .unwrap();

        let res = ctx_mgr.check_spec(&spec);

        assert_eq!(res, Some(path));
    }

    #[test]
    fn test_spec_reach_location_one_rule_one_process_no_guards() {
        let test_spec = "
            skel test_ta1 {
                shared var1, var2, var3;
                parameters n, f;
                
                assumptions (1) {
                    n > 3 * f;
                    n == 1;
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
                    0: loc1 -> loc2
                        when(true)
                        do {};
                }

                specifications (1) {
                    test1:
                        [](loc2 == 0)
                }
            }
            ";

        let ta = ByMCParser::new().parse_ta(test_spec).unwrap();

        let ctx_mgr = EContextMgr::new(ta.clone(), &[], &SMTSolverBuilder::default())
            .expect("Failed to create context manager");
        let spec = UpwardsClosedSet::new_cover([Location::new("loc2")]);

        let path = PathBuilder::new(ta)
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
                RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2")).build(),
                1,
            ))
            .unwrap()
            .add_configuration(Configuration::new(
                HashMap::from([
                    (Variable::new("var1"), 0),
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
            .build()
            .unwrap();

        let res = ctx_mgr.check_spec(&spec);

        assert_eq!(res, Some(path));
    }

    #[test]
    fn test_spec_reach_location_one_rule_5_process_no_guards() {
        let test_spec = "
            skel test_ta1 {
                shared var1, var2, var3;
                parameters n, f;
                
                assumptions (1) {
                    n > 3 * f;
                    n == 5;
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
                    0: loc1 -> loc2
                        when(true)
                        do {};
                }

                specifications (1) {
                    test1:
                        [](loc2 == 0)
                }
            }
            ";

        let ta = ByMCParser::new().parse_ta(test_spec).unwrap();

        let ctx_mgr = EContextMgr::new(ta.clone(), &[], &SMTSolverBuilder::default())
            .expect("Failed to create context manager");
        let spec =
            UpwardsClosedSet::new_reach([(Location::new("loc2"), 1)], [Location::new("loc1")]);

        let path = PathBuilder::new(ta)
            .add_parameter_assignment(HashMap::from([
                (Parameter::new("n"), 5),
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
                    (Location::new("loc1"), 5),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 0),
                ]),
            ))
            .unwrap()
            .add_transition(Transition::new(
                RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2")).build(),
                5,
            ))
            .unwrap()
            .add_configuration(Configuration::new(
                HashMap::from([
                    (Variable::new("var1"), 0),
                    (Variable::new("var2"), 0),
                    (Variable::new("var3"), 0),
                ]),
                HashMap::from([
                    (Location::new("loc1"), 0),
                    (Location::new("loc2"), 5),
                    (Location::new("loc3"), 0),
                ]),
            ))
            .unwrap()
            .build()
            .unwrap();

        let res = ctx_mgr.check_spec(&spec);

        assert_eq!(res, Some(path));
    }

    #[test]
    fn test_spec_unreachable_location_graph() {
        let test_spec = "
            skel test_ta1 {
                shared var1, var2, var3;
                parameters n, t, f;
                
                assumptions (1) {
                    n > 3 * f;
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
                    0: loc1 -> loc2
                        when(true)
                        do {};
                }

                specifications (1) {
                    test1:
                        [](loc3 == 0)
                }
            }
            ";

        let ta = ByMCParser::new().parse_ta(test_spec).unwrap();

        let ctx_mgr = EContextMgr::new(ta, &[], &SMTSolverBuilder::default())
            .expect("Failed to create context manager");
        let spec = UpwardsClosedSet::new_cover([Location::new("loc3")]);

        let res = ctx_mgr.check_spec(&spec);

        assert_eq!(res.clone(), None, "Error Path: {}", res.unwrap());
    }

    #[test]
    fn test_spec_reach_location_two_rules_one_guard() {
        let test_spec = "
            skel test_ta1 {
                shared var1, var2, var3;
                parameters n, f;
                
                assumptions (1) {
                    n > 3 * f;
                    n == 5;
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
                    0: loc1 -> loc2
                        when(var1 > 3 && var2 <= 0)
                        do {};
                    1: loc1 -> loc3
                        when(true)
                        do {var1' == var1 + 1};
                }

                specifications (1) {
                    test1:
                        [](loc2 == 0)
                }
            }
            ";

        let ta = ByMCParser::new().parse_ta(test_spec).unwrap();

        let ctx_mgr = EContextMgr::new(ta.clone(), &[], &SMTSolverBuilder::default())
            .expect("Failed to create context manager");
        let spec = UpwardsClosedSet::new_cover([Location::new("loc2")]);

        let path = PathBuilder::new(ta)
            .add_parameter_assignment(HashMap::from([
                (Parameter::new("n"), 5),
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
                    (Location::new("loc1"), 5),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 0),
                ]),
            ))
            .unwrap()
            .add_transition(Transition::new(
                RuleBuilder::new(1, Location::new("loc1"), Location::new("loc3"))
                    .with_action(Action::new_with_update(
                        Variable::new("var1"),
                        UpdateExpression::Inc(1),
                    ))
                    .build(),
                3,
            ))
            .unwrap()
            .add_configuration(Configuration::new(
                HashMap::from([
                    (Variable::new("var1"), 3),
                    (Variable::new("var2"), 0),
                    (Variable::new("var3"), 0),
                ]),
                HashMap::from([
                    (Location::new("loc1"), 2),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 3),
                ]),
            ))
            .unwrap()
            .add_transition(Transition::new(
                RuleBuilder::new(1, Location::new("loc1"), Location::new("loc3"))
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
                    (Location::new("loc3"), 4),
                ]),
            ))
            .unwrap()
            .add_transition(Transition::new(
                RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2"))
                    .with_guard(BooleanExpression::BinaryExpression(
                        Box::new(BooleanExpression::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                            ComparisonOp::Gt,
                            Box::new(IntegerExpression::Const(3)),
                        )),
                        BooleanConnective::And,
                        Box::new(BooleanExpression::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                            ComparisonOp::Leq,
                            Box::new(IntegerExpression::Const(0)),
                        )),
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
                    (Location::new("loc1"), 0),
                    (Location::new("loc2"), 1),
                    (Location::new("loc3"), 4),
                ]),
            ))
            .unwrap()
            .build()
            .unwrap();

        let res = ctx_mgr.check_spec(&spec);

        assert!(res.is_some());
        assert_eq!(
            res.clone(),
            Some(path.clone()),
            "Got:\n{}\n\nExpected:\n{}\n\n",
            res.unwrap(),
            path
        );
    }

    #[test]
    fn test_spec_reach_location_three_rules_one_guard_self_loop() {
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
                        [](loc2 == 0 || var2 > 6)
                }
            }
            ";

        let ta = ByMCParser::new().parse_ta(test_spec).unwrap();

        let ctx_mgr = EContextMgr::new(ta.clone(), &[], &SMTSolverBuilder::default())
            .expect("Failed to create context manager");
        let spec = UpwardsClosedSet::new_cover([Location::new("loc3")]);

        let path = PathBuilder::new(ta)
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
                3,
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

        let res = ctx_mgr.check_spec(&spec);

        assert!(res.is_some());
        assert_eq!(
            res.clone(),
            Some(path.clone()),
            "Got:\n{}\n\nExpected:\n{}\n\n",
            res.unwrap(),
            path
        );
    }
}
