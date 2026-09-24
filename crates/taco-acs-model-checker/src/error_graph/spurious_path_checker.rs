//! Check an error graph for non spurious paths

use log::debug;
use std::{
    collections::{HashMap, HashSet},
    ops::Deref,
    rc::Rc,
};
use taco_display_utils::join_iterator;
use taco_model_checker::{ModelCheckerResult, internal_spec::upwards_closed_set::UpwardsClosedSet};
use taco_smt_encoder::SMTSolverContext;
use taco_smt_encoder::expression_encoding::EncodeToSMT;
use taco_smt_encoder::expression_encoding::ctx_mgr::SMTConfigMgr;
use taco_smt_encoder::expression_encoding::step_ctx::LazyStepContext;
use taco_smt_encoder::{
    SMTSolver,
    expression_encoding::{
        DeclaresVariable,
        config_ctx::ConfigCtx,
        ta_encoding::{encode_initial_constraints, encode_resilience_condition},
    },
};
use taco_threshold_automaton::ThresholdAutomaton;

use crate::acs_threshold_automaton::configuration::ACSTAConfig;
use crate::{
    acs_threshold_automaton::ACSThresholdAutomaton,
    error_graph::{ErrorGraph, NodeRef},
};

/// Compact type alias for step contexts in this module
type StepCtx = LazyStepContext<ACSThresholdAutomaton, ConfigCtx>;

pub struct SpuriousGraphChecker {
    solver: SMTSolver,
    spec: UpwardsClosedSet,
    cs_ta: Rc<ACSThresholdAutomaton>,
    ctx_mgr: SMTConfigMgr<StepCtx, ConfigCtx>,
}

impl SpuriousGraphChecker {
    pub fn new(ta: &ACSThresholdAutomaton, spec: UpwardsClosedSet, mut solver: SMTSolver) -> Self {
        let params = Rc::new(
            ta.parameters()
                .map(|p| {
                    let expr = p
                        .declare_variable(&mut solver, 0)
                        .expect("Failed to declare parameter SMT variables");
                    solver
                        .assert(solver.gte(expr, solver.numeral(0)))
                        .expect("Failed to assert param gt 0");

                    (p.clone(), expr)
                })
                .collect::<HashMap<_, _>>(),
        );

        let ctx = ConfigCtx::new(&mut solver, ta, params.clone(), 0);

        // Encode the resilience conditions
        let rc = encode_resilience_condition(ta, &solver, &ctx);
        solver
            .assert(rc)
            .expect("Failed to assert resilience condition");

        // Encode the condition on the first variable
        let init_cond = encode_initial_constraints(ta, &solver, &ctx);
        solver
            .assert(init_cond)
            .expect("Failed to assert initial condition");

        let mut ctx_mgr = SMTConfigMgr::new(params);
        ctx_mgr.push_cfg(Rc::new(ctx));

        Self {
            solver,
            ctx_mgr,
            spec,
            cs_ta: Rc::new(ta.clone()),
        }
    }

    pub fn find_violation(&mut self, e_graph: &ErrorGraph) -> ModelCheckerResult {
        debug!(
            "Error graph exploration of ta '{}' and specification '{}' found the following initial configurations, that can potentially reach the error state: {}",
            self.cs_ta,
            self.spec,
            join_iterator(
                e_graph
                    .initial_leafs
                    .iter()
                    .map(|n| n.borrow().config().display_compact(&self.cs_ta)),
                ","
            )
        );

        for init_node in e_graph.initial_leafs.iter() {
            let init_cfg = self.ctx_mgr.configs().next().unwrap().clone();

            let res_check_node = self.explore_node_for_violation(init_node, init_cfg, 1);

            if !res_check_node.is_safe() {
                return res_check_node;
            }
        }

        ModelCheckerResult::SAFE
    }

    fn explore_node_for_violation(
        &mut self,
        node: &NodeRef,
        prev_cfg_ctx: Rc<ConfigCtx>,
        index: usize,
    ) -> ModelCheckerResult {
        // Push a new frame before encoding the conditions of this node
        // Should be popped before returning
        self.solver
            .push()
            .expect("Failed to push frame for configuration");

        let cfg_constr = node.borrow().config().encode_config_constraints_to_smt(
            &self.cs_ta,
            &self.solver,
            prev_cfg_ctx.deref(),
        );
        self.solver
            .assert(cfg_constr)
            .expect("Failed to assert configuration constraints");

        debug!(
            "Exploring configuration: {}",
            node.borrow().config().display_compact(&self.cs_ta)
        );

        // Spurious checks on error nodes will be conducted anyway
        if node.borrow().error_level() > 0
            && !self
                .solver
                .assert_and_check_expr(self.solver.true_())
                .expect("Failed to check spurious")
                .is_sat()
        {
            self.solver.pop().expect("Failed to pop frame");
            debug!("Explored path was spurious");
            return ModelCheckerResult::SAFE;
        }

        // Create a new context for the next configuration
        let cfg_primed_ctx = Rc::new(ConfigCtx::new(
            &mut self.solver,
            self.cs_ta.deref(),
            self.ctx_mgr.params().clone(),
            index,
        ));
        self.ctx_mgr.push_cfg_primed(cfg_primed_ctx.clone());

        // Compute the sequence of rules applicable for a steady path and
        // the nodes for step transitions
        let mut visited_nodes_cache = HashSet::<ACSTAConfig>::new();
        let (s, step_nodes, contains_err_state) =
            Self::collect_enabled_rules_and_next_nodes(node, &mut visited_nodes_cache);
        debug!(
            "Steady step with rules : {}",
            join_iterator(s.iter().map(|u| format!("'{u}'")), ",")
        );

        // Encode and assert the steady condition
        let steady_ctx: LazyStepContext<ACSThresholdAutomaton, ConfigCtx> = self
            .encode_and_assert_steady_path_with_rules(
                &s,
                prev_cfg_ctx,
                cfg_primed_ctx.clone(),
                index,
            );
        self.ctx_mgr.push_steady(steady_ctx);

        for node in step_nodes {
            // for each node and an edge to a new interval
            self.solver.push().expect("Failed to push frame");

            let res = self.explore_next_interval_state_transition(
                &node,
                cfg_primed_ctx.clone(),
                index + 1,
            );
            if !res.is_safe() {
                return res;
            }

            self.solver.pop().expect("Failed to pop frame");
        }

        // Currently in error state: Check spuriousness and return result
        if node.borrow().error_level() == 0 || (contains_err_state) {
            let res = self.check_spurious_error(&cfg_primed_ctx);
            if !res.is_safe() {
                return res;
            }
        }

        // current path is safe, remove the contexts assumptions
        self.solver
            .pop()
            .expect("Failed to pop frame for configuration");
        self.ctx_mgr.pop_steady();
        self.ctx_mgr.pop_cfg_primed();

        ModelCheckerResult::SAFE
    }

    fn explore_next_interval_state_transition(
        &mut self,
        next_node: &NodeRef,
        prev_cfg: Rc<ConfigCtx>,
        index: usize,
    ) -> ModelCheckerResult {
        let node = next_node.borrow();
        let is = node.config().interval_state().clone();

        // Create the variables for the next config
        let nxt_cfg = Rc::new(ConfigCtx::new(
            &mut self.solver,
            self.cs_ta.deref(),
            self.ctx_mgr.params().clone(),
            index,
        ));
        self.ctx_mgr.push_cfg(nxt_cfg.clone());

        // find outgoing transition (cannot be self-loop)
        for next_edge in node
            .parents()
            .chain(node.back_edges())
            .filter(|e| e.node().borrow().config().interval_state() != &is)
        {
            self.solver.push().expect("Failed to push context");

            debug!(
                "Exploring step to configuration '{}' using '{}'",
                next_edge
                    .node()
                    .borrow()
                    .config()
                    .display_compact(&self.cs_ta),
                join_iterator(next_edge.get_ids_of_rules(), ",")
            );

            let cfg_constr = node.config().encode_config_constraints_to_smt(
                &self.cs_ta,
                &self.solver,
                prev_cfg.deref(),
            );
            self.solver
                .assert(cfg_constr)
                .expect("Failed to assert configuration constraints");

            let rules = next_edge
                .get_ids_of_rules()
                .map(|id| {
                    self.cs_ta
                        .get_rule_by_id(id)
                        .expect("Failed to find rule id")
                })
                .cloned();

            let step_ctx = LazyStepContext::new(
                rules,
                self.cs_ta.clone(),
                prev_cfg.clone(),
                nxt_cfg.clone(),
                index,
                &mut self.solver,
            );
            self.ctx_mgr.push_step(step_ctx.clone());

            let step_constr = step_ctx.encode_phi_step(&self.solver);
            self.solver
                .assert(step_constr)
                .expect("Failed to assert step constraints");

            let res = self.explore_node_for_violation(next_edge.node(), nxt_cfg.clone(), index + 1);
            if !res.is_safe() {
                return res;
            }

            self.solver
                .pop()
                .expect("Failed to pop solver context after exploring step");
            self.ctx_mgr.pop_step();
        }

        self.ctx_mgr.pop_cfg();

        ModelCheckerResult::SAFE
    }

    fn encode_and_assert_steady_path_with_rules(
        &mut self,
        appl_rules: &HashSet<u32>,
        prev_cfg: Rc<ConfigCtx>,
        next_cfg: Rc<ConfigCtx>,
        index: usize,
    ) -> StepCtx {
        let rules_to_appl = appl_rules
            .iter()
            .map(|id| {
                self.cs_ta
                    .get_rule_by_id(*id)
                    .expect("Failed to find rule id")
            })
            .cloned();

        let step_ctx = LazyStepContext::new(
            rules_to_appl,
            self.cs_ta.clone(),
            prev_cfg,
            next_cfg,
            index,
            &mut self.solver,
        );

        let steady_path = step_ctx.encode_phi_steady(&self.solver);

        self.solver
            .assert(steady_path)
            .expect("Failed to assert steady condition");

        step_ctx
    }

    /// This function collects the orders in which rules are applicable while
    /// staying in the same interval state along with the rules that would allow
    /// to transition out of the interval state.
    ///
    /// The first set (`HashSet<u32>`) represents all applicable rules, and the
    /// second value is a vector of next nodes.
    /// - The second element (`Vec<NodeRef>`) contains nodes that represent possible transitions out of the current interval state.
    /// - The third element (`bool`) is true if any of the traversed nodes are in an error state, false otherwise.
    fn collect_enabled_rules_and_next_nodes(
        org_node: &NodeRef,
        visited_nodes: &mut HashSet<ACSTAConfig>,
    ) -> (HashSet<u32>, Vec<NodeRef>, bool) {
        let mut next_is = Vec::new();
        let mut applicable_rules = HashSet::new();
        let mut s_contains_err_state = false;

        let is = org_node.borrow().config().interval_state().clone();
        let node = org_node.borrow();

        // add node to visited set
        visited_nodes.insert(node.config().clone());

        // add self-loops
        applicable_rules.extend(node.self_loops());

        let mut exists_new_is = false;

        for successor_edge in node.parents().chain(node.back_edges()) {
            // Resets can enable back edges and cycles
            if successor_edge.node().borrow().config() == node.config() {
                applicable_rules.extend(successor_edge.get_ids_of_rules());
                continue;
            }

            // if we are remain in the same interval state, add all the rules
            // of the edge to the possible sequence of rules
            if successor_edge.node().borrow().config().interval_state() == &is {
                // Potentially, we are already in an error state
                if successor_edge.node().borrow().error_level() == 0 {
                    s_contains_err_state = true;
                }

                applicable_rules.extend(successor_edge.get_ids_of_rules());

                if !visited_nodes.contains(successor_edge.node().borrow().config()) {
                    // recursively compute applicable rules
                    let (s, nxt, suc_s_contains_err_state) =
                        Self::collect_enabled_rules_and_next_nodes(
                            successor_edge.node(),
                            visited_nodes,
                        );
                    s_contains_err_state |= suc_s_contains_err_state;
                    next_is.extend(nxt);
                    applicable_rules.extend(s);
                }

                continue;
            }

            exists_new_is = true;
        }

        if exists_new_is {
            next_is.push(org_node.clone());
        }

        (applicable_rules, next_is, s_contains_err_state)
    }

    // return true if spurious
    // removes the current context if spurious
    fn check_spurious_error(&mut self, ctx: &ConfigCtx) -> ModelCheckerResult {
        // encode error and check sat
        self.solver
            .push()
            .expect("Failed to push frame for err cond");

        let err_cond = self
            .spec
            .encode_to_smt_with_ctx(&self.solver, ctx)
            .expect("Failed to encode error condition");

        let res = self
            .solver
            .assert_and_check_expr(err_cond)
            .expect("Failed to check spurious");

        if res.is_sat() {
            let path = self.ctx_mgr.extract_error_path(
                res,
                &mut self.solver,
                self.cs_ta.get_interval_ta().get_ta().clone(),
            );
            return ModelCheckerResult::UNSAFE {
                violations: vec![(self.spec.to_string(), Box::new(path))],
                unknown: Vec::new(),
            };
        }

        self.solver
            .pop()
            .expect("Failed to pop frame for error condition");

        debug!("Checked for error, but error has not been reached.");

        ModelCheckerResult::SAFE
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use taco_interval_ta::IntervalThresholdAutomaton;
    use taco_model_checker::{
        ModelCheckerResult, TATrait, internal_spec::upwards_closed_set::UpwardsClosedSet,
    };
    use taco_parser::{ParseTA, bymc::ByMCParser};
    use taco_smt_encoder::SMTSolverBuilder;
    use taco_threshold_automaton::{
        expressions::{
            BooleanConnective, BooleanExpression, ComparisonOp, IntegerExpression, Location,
            Parameter, Variable,
        },
        general_threshold_automaton::{Action, UpdateExpression, builder::RuleBuilder},
        path::{Configuration, PathBuilder, Transition},
    };

    use crate::{acs_threshold_automaton::ACSThresholdAutomaton, error_graph::ErrorGraph};

    #[test]
    fn test_initial_error_condition_fullfilled() {
        let test_spec = "
            skel test_ta1 {
                shared var1, var2, var3;
                parameters n, f;
                
                assumptions (1) {
                    n == 1;
                }

                locations (2) {
                    loc1 : [0];
                    loc2 : [1];
                    loc3 : [2];
                }

                inits (1) {
                    loc1 == 0;
                    loc2 == n;
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
        let solver_builder = SMTSolverBuilder::default();

        let spec = UpwardsClosedSet::new_cover([Location::new("loc2")]);

        let test_tas =
            IntervalThresholdAutomaton::try_from_general_ta(ta.clone(), &solver_builder, &spec)
                .unwrap();
        assert_eq!(test_tas.len(), 1);

        let test_ta = test_tas[0].clone();

        let cs_ta = ACSThresholdAutomaton::from(test_ta);

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
                    (Location::new("loc1"), 0),
                    (Location::new("loc2"), 1),
                    (Location::new("loc3"), 0),
                ]),
            ))
            .unwrap()
            .build()
            .unwrap();

        let e_graph = ErrorGraph::compute_error_graph(spec, cs_ta);
        assert!(!e_graph.is_empty());

        let ctx = SMTSolverBuilder::default();
        let res = e_graph.check_for_non_spurious_counter_example(ctx.new_solver());
        assert!(!res.is_safe());

        let res = match res {
            ModelCheckerResult::SAFE => unreachable!("checked above"),
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
    fn test_spec_reach_location_one_rule_one_process_no_guards() {
        let test_spec = "
            skel test_ta1 {
                shared var1, var2, var3;
                parameters n, f;
                
                assumptions (1) {
                    n == 1;
                }

                locations (2) {
                    loc1 : [0];
                    loc2 : [1];
                    loc3 : [2];
                }

                inits (1) {
                    loc1 == 1;
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
        let solver_builder = SMTSolverBuilder::default();

        let spec = UpwardsClosedSet::new_cover([Location::new("loc2")]);

        let test_tas =
            IntervalThresholdAutomaton::try_from_general_ta(ta.clone(), &solver_builder, &spec)
                .unwrap();
        assert_eq!(test_tas.len(), 1);

        let test_ta = test_tas[0].clone();

        let cs_ta = ACSThresholdAutomaton::from(test_ta);

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

        let e_graph = ErrorGraph::compute_error_graph(spec, cs_ta);
        assert!(!e_graph.is_empty());

        let ctx = SMTSolverBuilder::default();
        let res = e_graph.check_for_non_spurious_counter_example(ctx.new_solver());
        assert!(!res.is_safe());

        let res = match res {
            ModelCheckerResult::SAFE => unreachable!("checked above"),
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
        let solver_builder = SMTSolverBuilder::default();

        let spec = UpwardsClosedSet::new_cover_int([(Location::new("loc2"), 5)]);

        let test_tas =
            IntervalThresholdAutomaton::try_from_general_ta(ta.clone(), &solver_builder, &spec)
                .unwrap();
        assert_eq!(test_tas.len(), 1);

        let test_ta = test_tas[0].clone();

        let cs_ta = ACSThresholdAutomaton::from(test_ta);

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
        let e_graph = ErrorGraph::compute_error_graph(spec, cs_ta);
        assert!(!e_graph.is_empty());

        let ctx = SMTSolverBuilder::default();
        let res = e_graph.check_for_non_spurious_counter_example(ctx.new_solver());
        assert!(!res.is_safe());

        let res = match res {
            ModelCheckerResult::SAFE => unreachable!("checked above"),
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
        let solver_builder = SMTSolverBuilder::default();

        let spec = UpwardsClosedSet::new_cover([Location::new("loc3")]);

        let test_tas =
            IntervalThresholdAutomaton::try_from_general_ta(ta.clone(), &solver_builder, &spec)
                .unwrap();
        assert_eq!(test_tas.len(), 1);

        let test_ta = test_tas[0].clone();

        let cs_ta = ACSThresholdAutomaton::from(test_ta);

        let e_graph = ErrorGraph::compute_error_graph(spec, cs_ta);
        assert!(e_graph.is_empty());

        let ctx = SMTSolverBuilder::default();
        let res = e_graph.check_for_non_spurious_counter_example(ctx.new_solver());
        assert!(res.is_safe());

        assert_eq!(res, ModelCheckerResult::SAFE);
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
                        when(var1 >= 4 && var2 <= 0)
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
        let solver_builder = SMTSolverBuilder::default();

        let spec = UpwardsClosedSet::new_cover([Location::new("loc2")]);

        let test_tas =
            IntervalThresholdAutomaton::try_from_general_ta(ta.clone(), &solver_builder, &spec)
                .unwrap();
        assert_eq!(test_tas.len(), 1);

        let test_ta = test_tas[0].clone();

        let cs_ta = ACSThresholdAutomaton::from(test_ta);

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
                    (Location::new("loc1"), 4),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 1),
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
                            ComparisonOp::Geq,
                            Box::new(IntegerExpression::Const(4)),
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

        let e_graph = ErrorGraph::compute_error_graph(spec, cs_ta);
        assert!(!e_graph.is_empty());

        let ctx = SMTSolverBuilder::default();
        let res = e_graph.check_for_non_spurious_counter_example(ctx.new_solver());
        assert!(!res.is_safe());

        let res = match res {
            ModelCheckerResult::SAFE => unreachable!("checked above"),
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
                        [](loc3 == 0)
                }
            }
            ";

        let ta = ByMCParser::new().parse_ta(test_spec).unwrap();
        let solver_builder = SMTSolverBuilder::default();

        let spec = UpwardsClosedSet::new_cover([Location::new("loc3")]);

        let test_tas =
            IntervalThresholdAutomaton::try_from_general_ta(ta.clone(), &solver_builder, &spec)
                .unwrap();
        assert_eq!(test_tas.len(), 1);

        let test_ta = test_tas[0].clone();

        let cs_ta = ACSThresholdAutomaton::from(test_ta);

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

        let e_graph = ErrorGraph::compute_error_graph(spec, cs_ta);
        assert!(!e_graph.is_empty());

        let ctx = SMTSolverBuilder::default();
        let res = e_graph.check_for_non_spurious_counter_example(ctx.new_solver());
        assert!(!res.is_safe());

        let res = match res {
            ModelCheckerResult::SAFE => unreachable!("checked above"),
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
}
