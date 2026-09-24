//! This module contains the definition of an smt_encoder
//! which is used to check if a steady error path is spurious or not.
//! It stores and manages all the smt variables that are constructed for the smt solver.

use std::cmp::min;
use std::fmt::{Debug, Display};
use std::rc::Rc;
use taco_display_utils::join_iterator;
use taco_model_checker::internal_spec::upwards_closed_set::UpwardsClosedSet;
use taco_threshold_automaton::lia_threshold_automaton::integer_thresholds::IntoNoDivBooleanExpr;

use easy_smt::Response::Sat;
use std::collections::HashMap;
use taco_interval_ta::IntervalThresholdAutomaton;
use taco_interval_ta::interval::Interval;

use taco_smt_encoder::SMTSolverBuilder;
use taco_smt_encoder::expression_encoding::DeclaresVariable;
use taco_smt_encoder::expression_encoding::EncodeToSMT;
use taco_smt_encoder::expression_encoding::config_ctx::{ConfigCtx, ConfigFromSMT};
use taco_smt_encoder::expression_encoding::{GetAssignment, SMTSolverError, SMTVariableContext};
use taco_smt_encoder::{SMTExpr, SMTSolverContext};
use taco_smt_encoder::{SMTSolution, SMTSolver};
use taco_threshold_automaton::ActionDefinition;
use taco_threshold_automaton::RuleDefinition;
use taco_threshold_automaton::ThresholdAutomaton;
use taco_threshold_automaton::VariableConstraint;
use taco_threshold_automaton::expressions::BooleanExpression;
use taco_threshold_automaton::expressions::{Location, Parameter, Variable};
use taco_threshold_automaton::general_threshold_automaton::Rule;
use taco_threshold_automaton::general_threshold_automaton::UpdateExpression;
use taco_threshold_automaton::general_threshold_automaton::UpdateExpression::*;
use taco_threshold_automaton::path::PathBuilder;
use taco_threshold_automaton::path::{Configuration, Path, Transition};

use crate::paths::{SteadyErrorPath, SteadyPath};

/// Type representing an SMT Encoder
/// which is used to encode a steady error path
/// and checking it for spuriousness.
pub struct SMTEncoderSteady<'a> {
    /// underlying Threshold Automaton
    ta: &'a IntervalThresholdAutomaton,
    /// vector of smt variables for each rule counter (counts how often this rule is applied)
    rule_counter_to_smt: Vec<(Rule, SMTExpr)>,
    /// indexed parameter context which stores the smt solver and manages all smt variables
    ctx: IndexedSMTContext,
    /// underlying steady error path
    steady_error_path: &'a SteadyErrorPath<'a>,
}
impl<'a> SMTEncoderSteady<'a> {
    /// Creates a new SMTEncoder for a given smt solver `smt`, a given threshold automaton `aut`
    /// and a `steady_error_path` that is checked for spuriousness.
    /// It automatically adds assertions for the resilience condition and the initial location and variable constraints to the smt solver.
    pub fn new(
        smt: SMTSolverBuilder,
        aut: &'a IntervalThresholdAutomaton,
        steady_error_path: &'a SteadyErrorPath<'a>,
    ) -> Self {
        // the number of configurations is given by the length of the abstract path
        let indexed_ctx = IndexedSMTContext::new(
            smt,
            // note that the number of configurations has to be multiplied by 2
            // since we always need a configuration at the beginning and end of a steady path
            (steady_error_path.length_configurations() * 2)
                .try_into()
                .unwrap(),
            aut,
        );

        let mut encoder = SMTEncoderSteady {
            rule_counter_to_smt: Vec::new(),
            ctx: indexed_ctx,
            ta: aut,
            steady_error_path,
        };

        // initialize all smt variables for rule counters
        encoder.initialize_rule_counters(steady_error_path.concrete_rules_ordered(aut));

        // encode resilience condition and initial assumptions
        let rc_cond = encoder.encode_resilience_conditions(aut.resilience_conditions());
        encoder
            .ctx
            .smt_solver
            .assert(rc_cond)
            .expect("error for asserting resilience condition");

        let loc_cond = encoder.encode_loc_conditions(aut.initial_location_constraints());
        encoder
            .ctx
            .smt_solver
            .assert(loc_cond)
            .expect("error for asserting initial location condition");

        let var_cond = aut
            .initial_variable_constraints()
            .map(|constr| constr.as_boolean_expr())
            .collect::<Vec<_>>();
        let var_cond = encoder.encode_var_conditions(var_cond.iter());
        encoder
            .ctx
            .smt_solver
            .assert(var_cond)
            .expect("error for asserting initial variable condition");

        encoder
    }

    /// creates and stores an smt variable for every Rule `rule` with its index in the iterator
    /// which counts how often `rule` is applied
    fn initialize_rule_counters<'b, I>(&mut self, rules_it: I)
    where
        I: Iterator<Item = &'b Rule>,
    {
        for (i, rule) in rules_it.enumerate() {
            let rule_smt = rule
                .declare_variable(&mut self.ctx.smt_solver, i.try_into().unwrap())
                .expect("Error creating shared smt variable");
            self.rule_counter_to_smt.push((rule.clone(), rule_smt));
        }
    }

    /// encodes and returns the resilience condition as an smt constraint
    fn encode_resilience_conditions<'b, I>(&mut self, rc: I) -> SMTExpr
    where
        I: Iterator<Item = &'b BooleanExpression<Parameter>>,
    {
        self.ctx.set_curr_index(0);
        let mut rc_encoding = self.ctx.smt_solver.true_();

        for param_constr in rc {
            let encoding = param_constr
                .encode_to_smt_with_ctx(&self.ctx.smt_solver, &self.ctx)
                .expect("error constructing the resilience condition");
            rc_encoding = self.ctx.smt_solver.and(rc_encoding, encoding);
        }

        rc_encoding
    }

    /// encodes and stores the initial location conditions into an smt constraint
    fn encode_loc_conditions<'b, I>(&mut self, cond: I) -> SMTExpr
    where
        I: Iterator<Item = &'b BooleanExpression<Location>>,
    {
        self.ctx.set_curr_index(0);
        let mut initial_loc_encoding = self.ctx.smt_solver.true_();

        for loc_constr in cond {
            let loc_encoding = loc_constr
                .encode_to_smt_with_ctx(&self.ctx.smt_solver, self.ctx.get_current_config_ctx())
                .expect("error constructing the initial location condition");
            initial_loc_encoding = self.ctx.smt_solver.and(initial_loc_encoding, loc_encoding);
        }

        initial_loc_encoding
    }

    /// encodes and stores the initial shared variable conditions into an smt constraint
    fn encode_var_conditions<'b, I>(&mut self, cond: I) -> SMTExpr
    where
        I: Iterator<Item = &'b BooleanExpression<Variable>>,
    {
        self.ctx.set_curr_index(0);
        let mut initial_var_encoding = self.ctx.smt_solver.true_();

        for var_constr in cond {
            let var_encoding = var_constr
                .encode_to_smt_with_ctx(&self.ctx.smt_solver, self.ctx.get_current_config_ctx())
                .expect("error constructing the initial shared variable condition");
            initial_var_encoding = self.ctx.smt_solver.and(initial_var_encoding, var_encoding);
        }

        initial_var_encoding
    }

    /// checks if the steady error path is non-spurious
    ///
    /// returns additionally Some(path) if a non-spurious error state is reached
    ///
    /// if the last state of the steady error path is an error state, the specification needs to be provided
    /// to ensure that the corresponding concrete state is also an error state
    ///
    /// 1. each indexed location, parameter, rule counter is non-negative
    /// 2. encode steady error path
    /// 3. encode that each steady path fragment is valid
    /// 4. encode error states if the last state of the steady error path is an error state
    /// 5. run smt solver
    pub fn steady_is_non_spurious(&mut self, spec: Option<&UpwardsClosedSet>) -> SpuriousResult {
        // 1. each indexed location, parameter, rule counter is non-negative
        for param_smt in self.ctx.param_to_smt.values() {
            let param_encoding = self
                .ctx
                .smt_solver
                .gte(*param_smt, self.ctx.smt_solver.numeral(0));
            self.ctx
                .smt_solver
                .assert(param_encoding)
                .expect("error for asserting a non-negative indexed location");
        }
        for loc in self.ta.locations() {
            for i in 0..self.steady_error_path.length_configurations() * 2 {
                let loc_smt = self.ctx.get_indexed_loc_smt(loc, i as usize);
                let loc_encoding = self
                    .ctx
                    .smt_solver
                    .gte(loc_smt, self.ctx.smt_solver.numeral(0));
                self.ctx
                    .smt_solver
                    .assert(loc_encoding)
                    .expect("error for asserting a non-negative indexed location");
            }
        }
        for (_, rule_counter) in self.rule_counter_to_smt.iter() {
            let rule_encoding = self
                .ctx
                .smt_solver
                .gte(*rule_counter, self.ctx.smt_solver.numeral(0));
            self.ctx
                .smt_solver
                .assert(rule_encoding)
                .expect("error for asserting a non-negative rule counter");
        }

        // 2. encode steady error path
        let abs = self.encode_steady_error_path();
        self.ctx
            .smt_solver
            .assert(abs)
            .expect("error for asserting encoded abstract path");

        // 3. encode that each steady error path fragment is valid
        let mut from_index: u32 = 0; // start from the first configuration after the initial one
        let mut rule_index = 0;
        for path in self.steady_error_path.steady_paths() {
            self.ctx
                .smt_solver
                .assert(self.encode_steady_path(from_index, rule_index, path))
                .expect("error for asserting steady path encoding");
            from_index += 2; // each steady path adds two configurations
            rule_index += path.length_transitions();
            if rule_index < self.rule_counter_to_smt.len() as u32 {
                self.ctx
                    .smt_solver
                    .assert(self.encode_step_transition(from_index, rule_index))
                    .expect("error for asserting step encoding");
                rule_index += 1; // each step applies one transition
            }
        }

        // 4. encode error states
        if let Some(specification) = spec {
            self.ctx
                .smt_solver
                .assert(self.encode_error_states(specification))
                .expect("error for asserting error states");
        }
        // 5. run smt solver
        let response = self
            .ctx
            .smt_solver
            .check()
            .expect("Error checking smt encoding");
        if response == Sat {
            // steady error path is non-spurious
            if spec.is_some() {
                // reached an error state
                let p = self
                    .extract_non_spurious_concrete_path(SMTSolution::SAT)
                    .expect("error extracting error path");
                return SpuriousResult::new(true, Some(p));
            }
            return SpuriousResult::new(true, None);
        }
        // steady error path is spurious
        SpuriousResult::new(false, None)
    }

    /// encodes that the step transition is valid
    ///
    /// by checking that the configuration after the steady path \sigma_i
    /// leads to the configuration of the next steady path \sigma_{i+1}
    /// by applying the transition r exactly once
    pub fn encode_step_transition(&self, from_index: u32, rule_index: u32) -> SMTExpr {
        let last_config_index = from_index - 1;
        let next_config_index = from_index;
        let (rule, rule_smt) = &self.rule_counter_to_smt[rule_index as usize];

        let mut step_encoding = self
            .ctx
            .smt_solver
            .eq(*rule_smt, self.ctx.smt_solver.numeral(1));

        // processes move according to the step transition
        let from_location = rule.source();
        let to_location = rule.target();

        let from_loc_smt = self
            .ctx
            .get_indexed_loc_smt(from_location, last_config_index as usize);
        let to_loc_smt = self
            .ctx
            .get_indexed_loc_smt(to_location, last_config_index as usize);
        let next_from_loc_smt = self
            .ctx
            .get_indexed_loc_smt(from_location, next_config_index as usize);
        let next_to_loc_smt = self
            .ctx
            .get_indexed_loc_smt(to_location, next_config_index as usize);
        if from_location == to_location {
            // self-loop, so no change in locations but at least one process has to be in the sending location
            step_encoding = self.ctx.smt_solver.and(
                step_encoding,
                self.ctx.smt_solver.eq(next_from_loc_smt, from_loc_smt),
            );
            step_encoding = self.ctx.smt_solver.and(
                step_encoding,
                self.ctx
                    .smt_solver
                    .gt(from_loc_smt, self.ctx.smt_solver.numeral(0)),
            );
        } else {
            // \sigma'.k[from] = \sigma.k[from] - c_i
            step_encoding = self.ctx.smt_solver.and(
                step_encoding,
                self.ctx.smt_solver.eq(
                    next_from_loc_smt,
                    self.ctx.smt_solver.sub(from_loc_smt, *rule_smt),
                ),
            );

            // \sigma'.k[from] = \sigma.k[from] + c_i
            step_encoding = self.ctx.smt_solver.and(
                step_encoding,
                self.ctx.smt_solver.eq(
                    next_to_loc_smt,
                    self.ctx.smt_solver.plus(to_loc_smt, *rule_smt),
                ),
            );
        }

        // all other locations unchanged
        for loc in self.ta.locations() {
            if loc != from_location && loc != to_location {
                let loc_smt = self
                    .ctx
                    .get_indexed_loc_smt(loc, last_config_index as usize);
                let next_loc_smt = self
                    .ctx
                    .get_indexed_loc_smt(loc, next_config_index as usize);
                step_encoding = self
                    .ctx
                    .smt_solver
                    .and(step_encoding, self.ctx.smt_solver.eq(next_loc_smt, loc_smt));
            }
        }

        // variables are updated according to the rule
        let action_map = rule
            .actions()
            .map(|action| (action.variable(), action.update().clone()))
            .collect::<HashMap<_, _>>();

        for shared_var in self.ta.variables() {
            let shared_smt = self
                .ctx
                .get_indexed_shared_smt(shared_var, last_config_index as usize);
            let next_shared_smt = self
                .ctx
                .get_indexed_shared_smt(shared_var, next_config_index as usize);
            let update = action_map
                .get(shared_var)
                .unwrap_or(&UpdateExpression::Unchanged);
            step_encoding = self.ctx.smt_solver.and(
                step_encoding,
                self.encode_update_shared_var(&shared_smt, &next_shared_smt, *rule_smt, update),
            );
        }

        step_encoding
    }

    /// encodes that shared variable 'x_i' is updated according to the update or reset
    /// of rule `r_i = (from, to, uv, τ, ϕ)` where `c_i` counts the number of times `r_i` is applied
    ///
    /// Encoding:
    /// - uv(x) != 0 => σ_{i+1}.g(x) = σ_i.g(x) + c_i * uv(x)
    /// - x ∈ τ => σ_{i+1}.g(x) = 0
    /// - uv(x) = 0 ∧ x ∉ τ => σ_{i+1}.g(x) = σ_i.g(x)
    fn encode_update_shared_var(
        &self,
        shared_smt: &SMTExpr,
        next_shared_smt: &SMTExpr,
        rule_smt: SMTExpr,
        update: &UpdateExpression,
    ) -> SMTExpr {
        match update {
            // σ_{i+1}.g(x) = σ_i.g(x) + c_i * uv(x)
            Inc(x) => self.ctx.smt_solver.eq(
                *next_shared_smt,
                self.ctx.smt_solver.plus(
                    *shared_smt,
                    self.ctx
                        .smt_solver
                        .times(rule_smt, self.ctx.smt_solver.numeral(*x)),
                ),
            ),
            // σ_{i+1}.g(x) = σ_i.g(x) - c_i * uv(x)
            Dec(x) => self.ctx.smt_solver.eq(
                *next_shared_smt,
                self.ctx.smt_solver.sub(
                    *shared_smt,
                    self.ctx
                        .smt_solver
                        .times(rule_smt, self.ctx.smt_solver.numeral(*x)),
                ),
            ),
            // σ_{i+1}.g(x) = 0
            UpdateExpression::Reset => self
                .ctx
                .smt_solver
                .eq(*next_shared_smt, self.ctx.smt_solver.numeral(0)),
            // σ_{i+1}.g(x) = σ_i.g(x)
            UpdateExpression::Unchanged => self.ctx.smt_solver.eq(*next_shared_smt, *shared_smt),
        }
    }

    /// encodes the interval constraints for an steady path
    ///
    /// i.e., it is checked if for each step, the shared variables are in the respective interval
    fn encode_steady_error_path(&mut self) -> SMTExpr {
        let mut encoding = self.ctx.smt_solver.true_();
        let mut index = 0;
        for steady_path in self.steady_error_path.steady_paths() {
            for (shared, interval) in steady_path
                .variable_assignment()
                .assignments()
                .filter(|(v, _)| !self.ta.get_helper_vars_for_sumvars().contains_key(*v))
            // do not encode the intervals of the replacement variables
            {
                self.ctx.set_curr_index(index);
                encoding = self.ctx.smt_solver.and(
                    encoding,
                    self.encode_shared_interval(shared.clone(), interval.clone()),
                );
                self.ctx.set_curr_index(index + 1);
                encoding = self.ctx.smt_solver.and(
                    encoding,
                    self.encode_shared_interval(shared.clone(), interval.clone()),
                );
            }
            // encode the intervals of the sums here instead
            // TODO: remove when ordering supports sums of variables
            for (shared, interval) in self.ta.get_helper_vars_for_sumvars().iter().map(|(v, sv)| {
                let interval = steady_path
                    .variable_assignment()
                    .assignments()
                    .find(|(var, _)| *var == v)
                    .expect("All variables should have an interval assignment")
                    .1;
                (sv, interval)
            }) {
                self.ctx.set_curr_index(index);
                encoding = self.ctx.smt_solver.and(
                    encoding,
                    self.encode_shared_interval(shared.clone(), interval.clone()),
                );
                self.ctx.set_curr_index(index + 1);
                encoding = self.ctx.smt_solver.and(
                    encoding,
                    self.encode_shared_interval(shared.clone(), interval.clone()),
                );
            }

            index += 2;
        }

        encoding
    }

    /// encodes that the value of an indexed shared variable 'x_i' is in the given interval,
    /// e.g., if 'x_i ∈ [t1,t2)' then: x_i ≥ t1 ∧ x_i < t2
    fn encode_shared_interval<S>(&self, shared: S, interval: Interval) -> SMTExpr
    where
        S: IntoNoDivBooleanExpr<Variable> + Clone,
    {
        let interval_expression = interval.encode_into_boolean_expr(&shared);
        interval_expression
            .encode_to_smt_with_ctx(&self.ctx.smt_solver, self.ctx.get_current_config_ctx())
            .expect("error encoding interval expression")
    }

    /// encodes the set of error states for the last configuration in the path
    ///
    /// This function works for any disjunction of Coverability, General Coverability and Reachability Specifications,
    /// For every other specification, `smt.false` is returned
    fn encode_error_states(&self, spec: &UpwardsClosedSet) -> SMTExpr {
        // TODO: refactor to not rely on internals
        spec.encode_to_smt_with_ctx(&self.ctx.smt_solver, self.ctx.config_ctxs.last().unwrap())
            .expect("Failed to encode error conditions")
    }

    /// encodes that the `steady path` with rules R = \{r_0,...,r_k\} is valid
    /// from = σ_{`from_index`} is the configuration at the beginning of the steady path
    /// to = σ'_{`from_index`+1} is the configuration at the end of the steady path
    ///
    /// rule_index indicates the first rule of the steady path in the rule_counter_to_smt vector
    ///
    /// 1. Processes move according to the steady path
    /// 2. Update shared variables 'x_0,...,x_n' according to the updates (resets or decrements are not allowed)
    /// 3. Make sure that for every rule in the steady path there is a fireable chain
    /// 4. If the error paths contains increments and decrements, ensure that monotonicity is preserved
    fn encode_steady_path(
        &self,
        from_index: u32,
        rule_index: u32,
        steady_path: &SteadyPath,
    ) -> SMTExpr {
        let mut steady_path_encoding =
            self.encode_steady_path_move_processes(from_index, rule_index, steady_path);
        steady_path_encoding = self.ctx.smt_solver.and(
            steady_path_encoding,
            self.encode_steady_path_update_shared_variables(from_index, rule_index, steady_path),
        );
        steady_path_encoding = self.ctx.smt_solver.and(
            steady_path_encoding,
            self.encode_steady_path_fireable_chain(from_index, rule_index, steady_path),
        );
        if self.ta.has_decrements() {
            steady_path_encoding = self.ctx.smt_solver.and(
                steady_path_encoding,
                self.encode_monotonicity_constraints(rule_index, steady_path),
            );
        }
        steady_path_encoding
    }

    /// encodes that the processes in the 'steady path' with rules R = \{r_0,...,r_k\} move accordingly
    /// from = σ_{`from_index`} is the configuration starting at the steady path
    /// to = σ'_{`from_index`+1} is the configuration ending at the steady path
    ///
    /// `rule_index` indicates the first rule of the steady path in the rule_counter_to_smt vector
    ///
    /// encoding:
    ///     ∀_{l_j ∈ L} σ'.k\[l_j\] = σ.k\[l_j\] + ∑_{r_i ∈ R with r_i.to = l_j} c_i - ∑_{r_i ∈ R with r_i.from = l_j} c_i
    fn encode_steady_path_move_processes(
        &self,
        from_index: u32,
        rule_index: u32,
        steady_path: &SteadyPath,
    ) -> SMTExpr {
        let mut move_encoding = self.ctx.smt_solver.true_();
        for loc in self.ta.locations() {
            let loc_smt = self.ctx.get_indexed_loc_smt(loc, from_index as usize);
            let next_loc_smt = self.ctx.get_indexed_loc_smt(loc, (from_index + 1) as usize);
            let mut rhs = loc_smt;
            for i in 0..steady_path.length_transitions() {
                let (rule, rule_smt) = self.rule_counter_to_smt[(rule_index + i) as usize].clone();
                if rule.target() == rule.source() {
                    // self-loop, so no change in locations
                    continue;
                }
                if rule.target() == loc {
                    // σ'.k[l_j] = σ.k[l_j] + ∑_{r_i ∈ R with r_i.to = l_j} c_i - ∑_{r_i ∈ R with r_i.from = l_j} c_i
                    rhs = self.ctx.smt_solver.plus(rhs, rule_smt);
                }
                if rule.source() == loc {
                    // σ'.k[l_j] = σ.k[l_j] + ∑_{r_i ∈ R with r_i.to = l_j} c_i - ∑_{r_i ∈ R with r_i.from = l_j} c_i
                    rhs = self.ctx.smt_solver.sub(rhs, rule_smt);
                }
            }
            move_encoding = self
                .ctx
                .smt_solver
                .and(move_encoding, self.ctx.smt_solver.eq(next_loc_smt, rhs));
        }

        move_encoding
    }

    /// encodes that the shared variables in the `steady path` with rules R = \{r_0,...,r_k\} are updated accordingly
    /// from = σ_{`from_index`} is the configuration at the beginning of the steady path
    /// to = σ'_{`from_index`+1} is the configuration at the end of the steady path
    ///
    /// `rule_index` indicates the first rule of the steady path in the rule_counter_to_smt vector
    ///
    /// returns an error if the steady path contains a reset or decrement update
    ///
    /// encoding:
    ///    ∀ x: σ'.g\[x\] = σ.g\[x\] + ∑_{r_i ∈ R} c_i * uv_i\[x\] if x is not reset
    ///    ∀ x: σ'.g\[x\] = 0 if x is reset
    fn encode_steady_path_update_shared_variables(
        &self,
        from_index: u32,
        rule_index: u32,
        steady_path: &SteadyPath,
    ) -> SMTExpr {
        let mut update_encoding = self.ctx.smt_solver.true_();
        for shared in self.ta.variables() {
            let shared_smt = self.ctx.get_indexed_shared_smt(shared, from_index as usize);
            let mut reset_shared = None;
            let next_shared_smt = self
                .ctx
                .get_indexed_shared_smt(shared, (from_index + 1) as usize);
            let mut rhs = shared_smt;
            for i in 0..steady_path.length_transitions() {
                let (rule, rule_smt) = self.rule_counter_to_smt[(rule_index + i) as usize].clone();
                let action_map = rule
                    .actions()
                    .map(|action| (action.variable(), action.update().clone()))
                    .collect::<HashMap<_, _>>();
                let update = action_map
                    .get(shared)
                    .unwrap_or(&UpdateExpression::Unchanged);
                match update {
                    Inc(x) => {
                        // σ'.g = σ.g + ∑_{r_i ∈ R} c_i * uv_i
                        rhs = self.ctx.smt_solver.plus(
                            rhs,
                            self.ctx
                                .smt_solver
                                .times(rule_smt, self.ctx.smt_solver.numeral(*x)),
                        );
                    }
                    Dec(x) => {
                        // σ'.g = σ.g - ∑_{r_i ∈ R} c_i * uv_i
                        rhs = self.ctx.smt_solver.sub(
                            rhs,
                            self.ctx
                                .smt_solver
                                .times(rule_smt, self.ctx.smt_solver.numeral(*x)),
                        );
                    }
                    // σ'.g[x] = 0
                    UpdateExpression::Reset => {
                        reset_shared = Some(
                            self.ctx
                                .smt_solver
                                .eq(next_shared_smt, self.ctx.smt_solver.numeral(0)),
                        );
                    }
                    UpdateExpression::Unchanged => {
                        continue;
                    }
                }
            }
            update_encoding = self.ctx.smt_solver.and(
                update_encoding,
                self.ctx.smt_solver.eq(next_shared_smt, rhs),
            );
            if let Some(reset_encoding) = reset_shared {
                update_encoding = self.ctx.smt_solver.and(update_encoding, reset_encoding);
            }
        }
        update_encoding
    }

    /// encodes that all the rules in the `steady path` with rules R = \{r_0,...,r_k\} lead to a fireable chain
    /// from = σ_{`from_index`} is the configuration at the beginning of steady path
    ///
    /// `rule_index` indicates the first rule of the steady path in the rule_counter_to_smt vector
    ///
    /// Compared to the version described in the main section of the paper, we
    /// statically filter the set S, to only include chains from R where for all i it
    /// holds that
    ///     r_i.to = r_{i+1}.from and r_s = r
    /// TODO add more tests
    fn encode_steady_path_fireable_chain(
        &self,
        from_index: u32,
        rule_index: u32,
        steady_path: &SteadyPath,
    ) -> SMTExpr {
        if rule_index == self.rule_counter_to_smt.len() as u32
            || steady_path.length_transitions() == 0
        {
            // no rules in the steady path, so trivially true
            return self.ctx.smt_solver.true_();
        }
        let vector_rules = self.rule_counter_to_smt
            [(rule_index as usize)..((rule_index + steady_path.length_transitions()) as usize)]
            .to_vec();
        let vector_cloned = vector_rules
            .iter()
            .map(|(rule, rule_smt)| (rule, rule_smt))
            .collect::<Vec<_>>();
        self.ctx
            .smt_solver
            .and_many(vector_rules.clone().into_iter().map(|(rule, rule_smt)| {
                // x_r > 0
                let xr_gt_0 = self
                    .ctx
                    .smt_solver
                    .gt(rule_smt, self.ctx.smt_solver.numeral(0));

                // S ∈ 2^R
                let all_possible_s =
                    self.compute_s_for_r_for_steady_path(&vector_cloned, &rule, &rule_smt);

                // prevent panics if there is no applicable chain
                if all_possible_s.is_empty() {
                    return self.ctx.smt_solver.false_();
                }

                // ∨_S ∈ 2^R ф_{chain}
                let disj_s = self.ctx.smt_solver.or_many(
                    all_possible_s
                        .iter()
                        .map(|s| self.encode_phi_chain_for_steady_path(from_index, s)),
                );

                //  x_r > 0 => ∨_S ∈ 2^R ф_{chain}
                self.ctx.smt_solver.imp(xr_gt_0, disj_s)
            }))
    }

    /// encodes that the rules applied in the `steady path` with rules R = \{r_0,...,r_k\}
    /// guarantee mononotonicity for the guards
    ///
    /// i.e., it ensures that no rule `r_i` which decrements a shared variable x is applied
    /// when a rule `r_j` which increments x is applied as well and vice versa
    ///
    /// `rule_index` indicates the first rule of the steady path in the rule_counter_to_smt vector
    ///
    /// encoding:
    ///     ∀_{x ∈ Γ} (∑_{r_i ∈ R with uv_i\[x\] > 0} c_i = 0) ∨ (∑_{r_i ∈ R with uv_i\[x\] < 0} c_i = 0)
    /// TODO: add more tests
    fn encode_monotonicity_constraints(
        &self,
        rule_index: u32,
        steady_path: &SteadyPath,
    ) -> SMTExpr {
        let mut monotonicity_encoding_constraints = Vec::new();
        for shared in self.ta.variables() {
            let mut inc_rules = Vec::new();
            let mut dec_rules = Vec::new();
            for i in 0..steady_path.length_transitions() {
                let (rule, rule_smt) = self.rule_counter_to_smt[(rule_index + i) as usize].clone();
                let action_map = rule
                    .actions()
                    .map(|action| (action.variable(), action.update().clone()))
                    .collect::<HashMap<_, _>>();
                let update = action_map
                    .get(shared)
                    .unwrap_or(&UpdateExpression::Unchanged);
                match update {
                    Inc(_) => inc_rules.push(rule_smt),
                    Dec(_) => dec_rules.push(rule_smt),
                    UpdateExpression::Reset | UpdateExpression::Unchanged => {}
                }
            }
            if inc_rules.is_empty() || dec_rules.is_empty() {
                // no increments or no decrements, so monotonicity is trivially satisfied
                continue;
            } else {
                let sum_inc = self.ctx.smt_solver.plus_many(inc_rules.iter().cloned());
                let sum_dec = self.ctx.smt_solver.plus_many(dec_rules.iter().cloned());
                let inc_eq_0 = self
                    .ctx
                    .smt_solver
                    .eq(sum_inc, self.ctx.smt_solver.numeral(0));
                let dec_eq_0 = self
                    .ctx
                    .smt_solver
                    .eq(sum_dec, self.ctx.smt_solver.numeral(0));
                // ∀_{x ∈ Γ} (∑_{r_i ∈ R with uv_i[x] > 0} c_i = 0) ∨ (∑_{r_i ∈ R with uv_i[x] < 0} c_i = 0)
                monotonicity_encoding_constraints.push(self.ctx.smt_solver.or(inc_eq_0, dec_eq_0));
            }
        }
        if monotonicity_encoding_constraints.is_empty() {
            // no increment and decrement for any shared variable, so monotonicity is trivially satisfied
            self.ctx.smt_solver.true_()
        } else {
            self.ctx
                .smt_solver
                .and_many(monotonicity_encoding_constraints)
        }
    }

    /// Encode ϕ_chain for a single non-deterministic guess for steady paths
    ///
    /// from_index indicates the index of the configuration at the beginning of the steady path
    ///
    /// This function encodes the ϕ_{chain} for set of rules s
    /// However, this function only encodes ∧_{r ∈ s} x_r > 0 ∧ σ.k(r_1.from) > 0
    /// as all other constraints can be statically checked during the
    /// computation of S
    ///
    /// Note: This function expects the sequence of rules to be reversed
    /// TODO: add more tests
    fn encode_phi_chain_for_steady_path(
        &self,
        from_index: u32,
        s: &[(&Rule, &SMTExpr)],
    ) -> SMTExpr {
        if s.is_empty() {
            return self.ctx.smt_solver.true_();
        }

        // σ.k(r_1.from) > 0
        let loc = s.last().unwrap().0.source(); // change if not reversed
        let loc_var = self.ctx.get_indexed_loc_smt(loc, from_index as usize);
        let loc_gt_0 = self
            .ctx
            .smt_solver
            .gt(loc_var, self.ctx.smt_solver.numeral(0));

        self.ctx.smt_solver.and_many(
            s.iter()
                .map(|(_, rule_smt)| {
                    self.ctx
                        .smt_solver
                        .gt(**rule_smt, self.ctx.smt_solver.numeral(0))
                })
                .chain([loc_gt_0]),
        )
    }

    /// Compute all sets possible values of S for rule r and 'steady path' with rules R = \{r_0,...,r_k\}
    ///
    /// This function computes all possible sets S for all rules r, where S is
    /// the set of rules from R that can lead up to r.
    /// Additionally, this function ensures that these sets are chainable,
    /// meaning they satisfy the formula:
    ///     ∧_{1< i ≤ s} r_{i-1}.to = r_i.from ∧ r_s = r
    ///
    /// This function uses the helper `compute_s_with_backtracking_recursive_for_steady_path`,
    /// to directly compute only chainable rule sequences.
    ///
    /// Note: **This function returns the sequences to apply in reversed
    /// order!**. You can use `.rev()` to iterate in reversed order.
    /// TODO: add more tests
    fn compute_s_for_r_for_steady_path(
        &'a self,
        vector_rules: &'a Vec<(&'a Rule, &'a SMTExpr)>,
        r: &'a Rule,
        rule_smt: &'a SMTExpr,
    ) -> Vec<Vec<(&'a Rule, &'a SMTExpr)>> {
        let loc = r.source();
        Self::compute_s_with_backtracking_recursive_for_steady_path(
            loc,
            vector_rules,
            vec![(r, rule_smt)],
        )
    }

    /// Recursive helper function that extends the returns a vector that
    /// contains:
    ///  - the current sequence of chainable rules
    ///  - the current sequence of rules extended with the incoming rules into
    ///    `loc`
    ///  - the chainable extensions for these rule sequences
    ///
    /// Note: Chains will be returned in reverse order !
    /// TODO: add more tests
    fn compute_s_with_backtracking_recursive_for_steady_path(
        loc: &'a Location,
        vector_rules: &[(&'a Rule, &'a SMTExpr)],
        rules_applied: Vec<(&'a Rule, &'a SMTExpr)>,
    ) -> Vec<Vec<(&'a Rule, &'a SMTExpr)>> {
        // get incoming rules into loc, these will be chainable
        let mut s = vector_rules
            .iter()
            .filter(|r| !rules_applied.contains(r) && r.0.target() == loc)
            .flat_map(|r| {
                let loc = r.0.source();
                let mut rules_applied: Vec<_> = rules_applied.clone();
                rules_applied.push(*r);

                Self::compute_s_with_backtracking_recursive_for_steady_path(
                    loc,
                    vector_rules,
                    rules_applied,
                )
            })
            .collect::<Vec<_>>();

        // current sequence is chainable, so add it
        s.push(rules_applied);

        s
    }

    /// extract a non-spurious counterexample trace reaching an error state from the smt solver
    fn extract_non_spurious_concrete_path(
        &mut self,
        res: SMTSolution,
    ) -> Result<Path, SMTEncoderError> {
        // path builder to construct an error path
        let path_builder = PathBuilder::new(self.ta.get_ta().clone());

        // extract parameters
        let mut param_assignment = HashMap::<Parameter, u32>::new();
        for param in self.ta.parameters() {
            if !res.is_sat() {
                return Err(SMTEncoderError::NoSatParamAssign(param.clone()));
            }

            let param_value = self
                .ctx
                .get_assignment(res, param)
                .expect("error getting assignment for parameter");
            match param_value {
                Some(value) => {
                    param_assignment.insert(param.clone(), value.try_into().unwrap());
                }
                None => {
                    return Err(SMTEncoderError::NoSatParamAssign(param.clone()));
                }
            }
        }

        let mut initialized_path_builder = path_builder
            .add_parameter_assignment(param_assignment)
            .expect("error adding parameter assignment");

        let configs = self.ctx.get_assigned_configs(res);

        let mut concrete_configs = Vec::from([configs[0].clone()]);
        let mut concrete_transitions = vec![];

        let mut config_index = 0;
        let mut rule_index = 0;
        for path in self.steady_error_path.steady_paths() {
            let (transitions, updated_configs) = self.extract_steady_path(
                res,
                path,
                &configs,
                concrete_configs.last().unwrap().clone(),
                config_index,
                rule_index,
            )?;
            concrete_configs.extend(updated_configs);
            concrete_transitions.extend(transitions);

            config_index += 2; // each steady path adds two configurations
            rule_index += path.length_transitions();
            if config_index < configs.len() as u32 {
                // extract step transition
                let (config, transition) =
                    self.extract_step_path(res, &configs, config_index, rule_index)?;
                concrete_configs.push(config);
                concrete_transitions.push(transition);
                rule_index += 1; // each step applies one transition
            }
        }

        initialized_path_builder = initialized_path_builder
            .add_configurations(concrete_configs)
            .expect("error adding configurations to path builder");
        initialized_path_builder = initialized_path_builder
            .add_transitions(concrete_transitions)
            .expect("error adding transitions to path builder");

        Ok(initialized_path_builder
            .build()
            .expect("error building the path"))
    }

    /// extracts the concrete step between two steady transitions
    fn extract_step_path(
        &mut self,
        res: SMTSolution,
        configurations: &[Configuration],
        config_index: u32,
        rule_index: u32,
    ) -> Result<(Configuration, Transition), SMTEncoderError> {
        // extract configuration
        let config = configurations[config_index as usize].clone();

        // add step transition to the path
        let rule_counter = self.rule_counter_to_smt[rule_index as usize].clone();
        let counter_value = self
            .get_rule_counter_assignment(res, &rule_counter.1)
            .expect("error getting rule counter assignment");

        match counter_value {
            Some(value) => {
                assert!(
                    value == 1,
                    "Step transition should be applied exactly once, but was applied {value} times!"
                );
                let transition = Transition::new(rule_counter.0, value.try_into().unwrap());
                Ok((config, transition))
            }
            None => Err(SMTEncoderError::NoSatRuleCounterAssign(
                rule_counter.0.clone(),
                rule_index,
            )),
        }
    }

    /// extracts the concrete path from a steady path
    fn extract_steady_path(
        &mut self,
        res: SMTSolution,
        steady_path: &SteadyPath,
        configurations: &[Configuration],
        last_config: Configuration,
        config_index: u32,
        rule_index: u32,
    ) -> Result<(Vec<Transition>, Vec<Configuration>), SMTEncoderError> {
        // extracts how often each rule of the cycle is applied
        let mut rules = Vec::<(Rule, u32)>::new();
        for i in 0..steady_path.length_transitions() {
            let index = (i + rule_index) as usize;
            let rule_counter = self.rule_counter_to_smt[index].clone();
            let counter_value = self
                .get_rule_counter_assignment(res, &rule_counter.1)
                .expect("error getting rule counter assignment");
            match counter_value {
                Some(value) => {
                    rules.push((rule_counter.0, value.try_into().unwrap()));
                }
                None => {
                    return Err(SMTEncoderError::NoSatRuleCounterAssign(
                        rule_counter.0.clone(),
                        index.try_into().unwrap(),
                    ));
                }
            }
        }

        rules = rules
            .into_iter()
            .filter(|(_, n)| *n > 0)
            .collect::<Vec<_>>();

        let mut curr_config = last_config.clone();

        let mut concrete_configs = vec![];
        let mut concrete_transitions = vec![];

        let old_rules = rules.clone();
        let old_config = curr_config.clone();

        // Try to order rules such that they are chainable
        while !rules.is_empty() {
            let mut n_apply = 0;

            // Add enabled self-loops first
            for (rule, n_to_apply) in rules.iter_mut().filter(|(r, _)| r.source() == r.target()) {
                if curr_config.get_processes_in_location(rule.source()) > 0 {
                    // if the transition is a self-loop apply it n_to_apply_times
                    n_apply = *n_to_apply;
                    *n_to_apply = 0;

                    let (transition, config) = Self::extract_transition_and_updated_config(
                        curr_config.clone(),
                        rule.clone(),
                        n_apply,
                    );
                    curr_config = config;
                    concrete_configs.push(curr_config.clone());
                    concrete_transitions.push(transition);
                }
            }

            for (rule, n_to_apply) in rules.iter_mut().filter(|(_, n)| *n > 0) {
                // Check if rule can be applied
                if curr_config.get_processes_in_location(rule.source()) > 0 {
                    // compute the number of times it can be applied
                    n_apply = min(
                        curr_config.get_processes_in_location(rule.source()),
                        *n_to_apply,
                    );

                    *n_to_apply -= n_apply;

                    let (transition, config) = Self::extract_transition_and_updated_config(
                        curr_config,
                        rule.clone(),
                        n_apply,
                    );
                    curr_config = config;
                    concrete_configs.push(curr_config.clone());
                    concrete_transitions.push(transition);

                    // check if there are new self loops enabled after updating
                    // the configuration
                    break;
                }
            }

            assert!(
                n_apply > 0,
                "Failed to order rules into chainable order! Configuration that rules must be applied on:\n{}\n\nRules left to apply:\n{}\n\nSet of rules to be ordered in this steady step:\n{}\n\nInitial configuration of the steady step:\n{}\n\n ",
                curr_config,
                join_iterator(rules.iter().map(|(r, i)| format!("{i} x {r}")), ",\n"),
                join_iterator(old_rules.iter().map(|(r, i)| format!("{i} x {r}")), ",\n"),
                old_config,
            );

            rules.retain(|(_, n)| *n > 0);
        }

        // check that the last configuration is the same as from the smt solver
        let i = config_index + 1;

        let correct_config = configurations[i as usize].clone();

        if correct_config != last_config {
            assert!(concrete_configs.last().unwrap().clone() == correct_config);
        }

        Ok((concrete_transitions, concrete_configs))
    }

    /// Create the transition that applies rule `rule` `n` times and compute the
    /// resulting configuration
    fn extract_transition_and_updated_config(
        config: Configuration,
        rule: Rule,
        n: u32,
    ) -> (Transition, Configuration) {
        let transition = Transition::new(rule, n);
        let curr_config = config
            .apply_rule(&transition)
            .expect("Constructed Transition invalid!");

        (transition, curr_config)
    }

    /// returns a satisying assignment for a given rule counter given as SMTExpr
    fn get_rule_counter_assignment(
        &mut self,
        res: SMTSolution,
        expr: &SMTExpr,
    ) -> Result<Option<u64>, SMTSolverError> {
        match res {
            SMTSolution::SAT => {
                let solver = self.ctx.get_smt_solver_mut();

                let solution = solver.get_value(vec![*expr])?;
                debug_assert!(solution.len() == 1);
                debug_assert!(solution[0].0 == *expr);

                let solution_val = solver.get(solution[0].1);

                Ok(Some(u64::try_from(solution_val).unwrap()))
            }
            SMTSolution::UNSAT => Ok(None),
        }
    }
}

/// Custom struct that stores the result of the Spurious Check
pub struct SpuriousResult {
    /// indicates if the abstract path is non spurious
    is_non_spurious: bool,
    /// optional path that is non-spurious
    non_spurious_path: Option<Path>,
}
impl SpuriousResult {
    /// creates a new SMTSpuriousResult
    pub fn new(is_non_spurious: bool, non_spurious_path: Option<Path>) -> Self {
        SpuriousResult {
            is_non_spurious,
            non_spurious_path,
        }
    }
    /// returns a new SMTSpuriousResult indicating that the abstract path is spurious
    pub fn new_spurious() -> Self {
        SpuriousResult {
            is_non_spurious: false,
            non_spurious_path: None,
        }
    }
    /// returns true if the abstract path is spurious
    pub fn is_non_spurious(&self) -> bool {
        self.is_non_spurious
    }

    /// returns the non-spurious path if it exists
    pub fn non_spurious_path(&self) -> Option<&Path> {
        self.non_spurious_path.as_ref()
    }
}

/// Custom Error type to indicate an error
/// when calling the `SMTEncoder`
#[derive(Debug, Clone)]
#[allow(clippy::enum_variant_names)]
enum SMTEncoderError {
    /// Error indicating that there is no satisfying assignment for a given parameter
    NoSatParamAssign(Parameter),
    /// Error indicating that there is no satisfying assignemnt for a given rule counter
    NoSatRuleCounterAssign(Rule, u32),
}

impl std::error::Error for SMTEncoderError {}

impl Display for SMTEncoderError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SMTEncoderError::NoSatParamAssign(param) => write!(
                f,
                "There exists no satisfying assignment for parameter {param}"
            ),
            SMTEncoderError::NoSatRuleCounterAssign(rule, i) => write!(
                f,
                "There exists no satisfying assignment for rule {rule} at index {i}",
            ),
        }
    }
}

/// An indexed SMT Context which creates and manages smt variables for parameters
/// and indexed smt variables for Locations, Variables and Rules
///
/// The context keeps track of the current index for locations, variables and rules
struct IndexedSMTContext {
    /// smt solver which used to evaluate SMT constraints
    smt_solver: SMTSolver,
    /// smt variable contexts for configurations
    config_ctxs: Vec<ConfigCtx>,
    /// mapping from parameter to smt variable
    param_to_smt: Rc<HashMap<Parameter, SMTExpr>>,
    /// current index
    curr_index: usize,
}
impl IndexedSMTContext {
    /// creates a new IndexedSMTContext that creates smt variables
    /// for all indexed locations and shared variables up to index `len`,
    /// and all parameters
    fn new<T: ThresholdAutomaton>(solver_builder: SMTSolverBuilder, len: usize, ta: &T) -> Self {
        let mut solver = solver_builder.new_solver();

        // initialize parameter variables
        let param_to_smt = ta
            .parameters()
            .map(|p| {
                let smt = p
                    .declare_variable(&mut solver, 0)
                    .expect("Failed to declare parameter");
                (p.clone(), smt)
            })
            .collect::<HashMap<_, _>>();
        let param_to_smt = Rc::new(param_to_smt);

        let config_ctxs = (0..len)
            .map(|index| ConfigCtx::new(&mut solver, ta, param_to_smt.clone(), index))
            .collect();

        IndexedSMTContext {
            smt_solver: solver,
            config_ctxs,
            param_to_smt,
            curr_index: 0,
        }
    }

    /// updates the current index
    fn set_curr_index(&mut self, i: usize) {
        self.curr_index = i
    }

    /// Get the current configuration context
    // TODO: refactor such that this not necessary
    fn get_current_config_ctx(&self) -> &ConfigCtx {
        &self.config_ctxs[self.curr_index]
    }
    /// Get the smt expression for the indexed shared variable at index `i`
    // TODO: refactor such that this not necessary
    fn get_indexed_shared_smt(&self, var: &Variable, i: usize) -> SMTExpr {
        self.config_ctxs[i]
            .get_expr_for(var)
            .expect("Failed to encode variable")
    }
    /// Get the smt expression for the indexed location at index `i`
    // TODO: refactor such that this not necessary
    fn get_indexed_loc_smt(&self, loc: &Location, i: usize) -> SMTExpr {
        self.config_ctxs[i]
            .get_expr_for(loc)
            .expect("Failed to encode location")
    }

    /// Extract the assigned configurations
    fn get_assigned_configs(&mut self, res: SMTSolution) -> Vec<Configuration> {
        self.config_ctxs
            .iter()
            .map(|cfg_ctx| {
                cfg_ctx
                    .get_assigned_configuration(&mut self.smt_solver, res)
                    .expect("Failed to extract configuration assignment")
            })
            .collect()
    }
}

impl SMTSolverContext for IndexedSMTContext {
    fn get_smt_solver(&self) -> &SMTSolver {
        &self.smt_solver
    }

    fn get_smt_solver_mut(&mut self) -> &mut SMTSolver {
        &mut self.smt_solver
    }
}

impl SMTVariableContext<Parameter> for IndexedSMTContext {
    fn get_expr_for(&self, param: &Parameter) -> Result<SMTExpr, SMTSolverError> {
        self.param_to_smt
            .get(param)
            .cloned()
            .ok_or_else(|| SMTSolverError::UndeclaredParameter(param.clone()))
    }

    fn get_exprs<'a>(&'a self) -> impl IntoIterator<Item = &'a Parameter>
    where
        Parameter: 'a,
    {
        self.param_to_smt.keys()
    }
}
impl GetAssignment<Parameter> for IndexedSMTContext {}

/// This context allows to use a custom SMT expression instead of a variable
/// when encoding expressions into SMT
struct _ReplacingContext {
    var_to_smt: HashMap<Variable, SMTExpr>,
    param: Rc<HashMap<Parameter, SMTExpr>>,
}

impl _ReplacingContext {
    /// Create a new ReplacingContext
    fn _new(
        var_to_smt: HashMap<Variable, SMTExpr>,
        param: Rc<HashMap<Parameter, SMTExpr>>,
    ) -> Self {
        Self { var_to_smt, param }
    }
}

impl SMTVariableContext<Variable> for _ReplacingContext {
    fn get_expr_for(&self, expr: &Variable) -> Result<SMTExpr, SMTSolverError> {
        self.var_to_smt
            .get(expr)
            .cloned()
            .ok_or_else(|| SMTSolverError::UndeclaredVariable(expr.clone()))
    }

    fn get_exprs<'a>(&'a self) -> impl IntoIterator<Item = &'a Variable>
    where
        Variable: 'a,
    {
        self.var_to_smt.keys()
    }
}

impl SMTVariableContext<Parameter> for _ReplacingContext {
    fn get_expr_for(&self, expr: &Parameter) -> Result<SMTExpr, SMTSolverError> {
        self.param
            .get(expr)
            .cloned()
            .ok_or_else(|| SMTSolverError::UndeclaredParameter(expr.clone()))
    }

    fn get_exprs<'a>(&'a self) -> impl IntoIterator<Item = &'a Parameter>
    where
        Parameter: 'a,
    {
        self.param.keys()
    }
}

#[cfg(test)]
mod tests {
    use crate::paths::SteadyErrorPath;
    use crate::paths::SteadyPath;
    use crate::paths::VariableAssignment;
    use crate::zcs::SymbolicVariableAssignment;
    use crate::zcs::builder::ZCSBuilder;
    use crate::zcs_error_graph::ZCSErrorGraph;
    use crate::zcs_error_graph::builder::ZCSErrorGraphBuilder;
    use taco_interval_ta::builder::IntervalTABuilder;

    use taco_interval_ta::IntervalThresholdAutomaton;
    use taco_model_checker::internal_spec::upwards_closed_set::UpwardsClosedSet;
    use taco_smt_encoder::SMTSolverBuilder;

    use taco_threshold_automaton::BooleanVarConstraint;
    use taco_threshold_automaton::LocationConstraint;
    use taco_threshold_automaton::ParameterConstraint;

    use crate::ZCSStates;
    use crate::smt_encoder_steady::SMTEncoderError;
    use crate::smt_encoder_steady::SMTEncoderSteady;
    use crate::smt_encoder_steady::SMTSolution;
    use crate::zcs::SymbolicTransition;
    use std::collections::HashMap;
    use std::collections::HashSet;
    use taco_interval_ta::interval::Interval;
    use taco_interval_ta::interval::IntervalBoundary;
    use taco_threshold_automaton::RuleDefinition;
    use taco_threshold_automaton::ThresholdAutomaton;
    use taco_threshold_automaton::expressions::ComparisonOp;
    use taco_threshold_automaton::expressions::IntegerExpression;
    use taco_threshold_automaton::expressions::fraction::Fraction;
    use taco_threshold_automaton::expressions::{Location, Parameter, Variable};
    use taco_threshold_automaton::general_threshold_automaton::Action;
    use taco_threshold_automaton::general_threshold_automaton::UpdateExpression;
    use taco_threshold_automaton::general_threshold_automaton::builder::RuleBuilder;
    use taco_threshold_automaton::lia_threshold_automaton::integer_thresholds::Threshold;

    /// Construct the following abstract threshold automaton:
    ///
    /// Threshold Automaton:
    /// Locations: {l0,l1,l2}
    /// Initial location: l0
    /// Parameter: {n,t,f}
    /// Shared Variable: x
    /// Resilience Condition: n > 3 * t & t >= f
    /// Initial location constraints: l0 = n - t & l1 = 0 & l2 = 0
    /// Initial variable constraints: x = 0
    /// Rules:
    ///     r0: l0 -> l1, guard: true, action: x = x + 1
    ///     r1: l0 -> l1, guard: true, action: x = x - 1
    ///     r2: l0 -> l1, guard: true, action: x = 0
    ///     r3: l1 -> l2, guard: x >= n - t, action: none
    ///     r4: l1 -> l2, guard: x >= n - t, action: x = x + 1
    ///
    /// Abstract Thershold Automaton:
    /// Intervals for x: I_0 = [0,1), I_1 = [1,n-t), I_2 = [n-t, infty)
    /// Interval Order: I_0 < I_1 < I_2
    /// Abstract Rules:
    ///     r0: l0 -> l1, guard: true, action: x = x + 1
    ///     r1: l0 -> l1, guard: true, action: x = x - 1
    ///     r2: l0 -> l1, guard: true, action: x = 0
    ///     r3: l1 -> l2, guard: x = I_2, action: none
    ///     r4: l1 -> l2, guard: x = I_2, action: x = x + 1
    fn get_test_automaton() -> IntervalThresholdAutomaton {
        let ta_builder =
            taco_threshold_automaton::general_threshold_automaton::builder::GeneralThresholdAutomatonBuilder::new("test")
                .with_locations(vec![
                    Location::new("l0"),
                    Location::new("l1"),
                    Location::new("l2"),
                ])
                .unwrap()
                .with_variable(Variable::new("x"))
                .unwrap()
                .with_parameters(vec![
                    Parameter::new("n"),
                    Parameter::new("t"),
                    Parameter::new("f"),
                ])
                .unwrap()
                .initialize()
                .with_resilience_conditions(vec![
                    ParameterConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Parameter::new("n"))),
                        ComparisonOp::Gt,
                        Box::new(
                            IntegerExpression::Const(3)
                                * IntegerExpression::Param(Parameter::new("t")),
                        ),
                    ),
                    ParameterConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Parameter::new("t"))),
                        ComparisonOp::Geq,
                        Box::new(IntegerExpression::Param(Parameter::new("f"))),
                    ),
                    ParameterConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Parameter::new("n"))),
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                    ParameterConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Parameter::new("t"))),
                        ComparisonOp::Geq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                    ParameterConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Parameter::new("f"))),
                        ComparisonOp::Geq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                    ParameterConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Parameter::new("n")) - IntegerExpression::Atom(Parameter::new("t"))),
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(1)),
                    ),
                ])
                .unwrap()
                .with_initial_location_constraints(vec![
                    LocationConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("l0"))),
                        ComparisonOp::Eq,
                        Box::new(
                            IntegerExpression::Param(Parameter::new("n"))
                                - IntegerExpression::Param(Parameter::new("t")),
                        ),
                    ),
                    LocationConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("l1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                    LocationConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("l2"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                ])
                .unwrap()
                .with_rules(vec![
                    RuleBuilder::new(0, Location::new("l0"), Location::new("l1"))
                        .with_action(
                            Action::new(
                                Variable::new("x"),
                                IntegerExpression::Atom(Variable::new("x"))
                                    + IntegerExpression::Const(1),
                            )
                            .unwrap(),
                        )
                        .build(),
                    RuleBuilder::new(1, Location::new("l0"), Location::new("l1"))
                        .with_action(
                            Action::new(
                                Variable::new("x"),
                                IntegerExpression::Atom(Variable::new("x"))
                                    - IntegerExpression::Const(1),
                            )
                            .unwrap(),
                        )
                        .build(),
                    RuleBuilder::new(2, Location::new("l0"), Location::new("l1"))
                        .with_action(Action::new_reset(Variable::new("x")))
                        .build(),
                    RuleBuilder::new(3, Location::new("l1"), Location::new("l2"))
                        .with_guard(BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("x"))),
                            ComparisonOp::Geq,
                            Box::new(
                                IntegerExpression::Param(Parameter::new("n"))
                                    - IntegerExpression::Param(Parameter::new("t")),
                            ),
                        ))
                        .build(),
                    RuleBuilder::new(4, Location::new("l1"), Location::new("l2"))
                        .with_guard(BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("x"))),
                            ComparisonOp::Geq,
                            Box::new(
                                IntegerExpression::Param(Parameter::new("n"))
                                    - IntegerExpression::Param(Parameter::new("t")),
                            ),
                        ))
                        .with_action(
                            Action::new(
                                Variable::new("x"),
                                IntegerExpression::Atom(Variable::new("x"))
                                    + IntegerExpression::Const(1),
                            )
                            .unwrap(),
                        )
                        .build(),
                ])
                .unwrap();
        let ta = ta_builder.build();
        let lia =
            taco_threshold_automaton::lia_threshold_automaton::LIAThresholdAutomaton::try_from(
                ta.clone(),
            )
            .unwrap();

        let mut interval_tas = IntervalTABuilder::new(lia, SMTSolverBuilder::default(), vec![])
            .build()
            .unwrap();
        let ata = interval_tas.next().unwrap();

        let nxt = interval_tas.next();
        assert!(nxt.is_none(), "Got additional ta {}", nxt.unwrap());
        ata
    }

    fn get_test_error_graph(ata: &'_ IntervalThresholdAutomaton) -> ZCSErrorGraph<'_> {
        let mgr = taco_bdd::BDDManager::default();
        let builder: ZCSBuilder = ZCSBuilder::new(&mgr, ata);
        let cs = builder.build();

        let l0 = cs.get_sym_state_for_loc(&Location::new("l0"));
        let l1 = cs.get_sym_state_for_loc(&Location::new("l1"));
        let l2 = cs.get_sym_state_for_loc(&Location::new("l2"));
        let error_states = l0
            .complement()
            .intersection(&l1.complement())
            .intersection(&l2);

        let error_graph_builder = ZCSErrorGraphBuilder::new(cs, error_states);
        error_graph_builder.build()
    }

    // initializes a steady error path that
    // that applies the step transitions r_0, r_1, r_0, r_3, r_2, r_4 and switches the interval for x from I_0 to I_1 to I_2
    // note that this path is spurious since r_2 resets x to 0
    fn get_test_steady_error_path<'a>(
        aut: &'a IntervalThresholdAutomaton,
        error_graph: &'a ZCSErrorGraph,
    ) -> SteadyErrorPath<'a> {
        let full_state = error_graph.new_empty_sym_state().complement();
        let true_bdd = full_state.set_of_states();
        let idle_sym_state = ZCSStates::new(true_bdd.clone());

        let r_0 = aut.rules().find(|r| r.id() == 0).unwrap();
        let r_1 = aut.rules().find(|r| r.id() == 1).unwrap();
        let r_2 = aut.rules().find(|r| r.id() == 2).unwrap();
        let r_3 = aut.rules().find(|r| r.id() == 3).unwrap();
        let r_4 = aut.rules().find(|r| r.id() == 4).unwrap();

        // I = [0,1)
        let interval_0 = Interval::new(
            IntervalBoundary::from_const(0),
            false,
            IntervalBoundary::from_const(1),
            true,
        );

        // I = [1, n-t)
        let interval_1 = Interval::new(
            IntervalBoundary::from_const(1),
            false,
            IntervalBoundary::Bound(Threshold::new(
                [
                    (Parameter::new("n"), 1.into()),
                    (Parameter::new("t"), Fraction::new(1, 1, true)),
                ],
                0,
            )),
            true,
        );
        // I = [n-t, \infty)
        let interval_2 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(
                [
                    (Parameter::new("n"), 1.into()),
                    (Parameter::new("t"), Fraction::new(1, 1, true)),
                ],
                0,
            )),
            false,
            IntervalBoundary::new_infty(),
            true,
        );

        let intial_assignment = VariableAssignment::new_for_testing(HashMap::from([(
            Variable::new("x"),
            interval_0.clone(),
        )]));
        let sym_initial_assignment =
            SymbolicVariableAssignment::new(true_bdd.clone(), intial_assignment);
        let mut steady_error_path = SteadyErrorPath::new(
            SteadyPath::new(
                vec![&SymbolicTransition::new(true_bdd.clone(), r_0.clone())],
                idle_sym_state.clone(),
                sym_initial_assignment,
            ),
            error_graph,
        );

        let sym_assignment = SymbolicVariableAssignment::new(
            true_bdd.clone(),
            VariableAssignment::new_for_testing(HashMap::from([(
                Variable::new("x"),
                interval_1.clone(),
            )])),
        );
        steady_error_path.add_successor(
            &SymbolicTransition::new(true_bdd.clone(), r_0.clone()),
            SteadyPath::new(
                vec![&SymbolicTransition::new(true_bdd.clone(), r_0.clone())],
                idle_sym_state.clone(),
                sym_assignment.clone(),
            ),
        );

        steady_error_path.add_successor(
            &SymbolicTransition::new(true_bdd.clone(), r_1.clone()),
            SteadyPath::new(
                vec![&SymbolicTransition::new(true_bdd.clone(), r_0.clone())],
                idle_sym_state.clone(),
                sym_assignment.clone(),
            ),
        );

        let sym_assignment = SymbolicVariableAssignment::new(
            true_bdd.clone(),
            VariableAssignment::new_for_testing(HashMap::from([(
                Variable::new("x"),
                interval_2.clone(),
            )])),
        );

        steady_error_path.add_successor(
            &SymbolicTransition::new(true_bdd.clone(), r_0.clone()),
            SteadyPath::new(
                vec![&SymbolicTransition::new(true_bdd.clone(), r_0.clone())],
                idle_sym_state.clone(),
                sym_assignment.clone(),
            ),
        );

        steady_error_path.add_successor(
            &SymbolicTransition::new(true_bdd.clone(), r_3.clone()),
            SteadyPath::new(vec![], idle_sym_state.clone(), sym_assignment),
        );

        let sym_assignment = SymbolicVariableAssignment::new(
            true_bdd.clone(),
            VariableAssignment::new_for_testing(HashMap::from([(
                Variable::new("x"),
                interval_0.clone(),
            )])),
        );

        steady_error_path.add_successor(
            &SymbolicTransition::new(true_bdd.clone(), r_2.clone()),
            SteadyPath::new(vec![], idle_sym_state.clone(), sym_assignment.clone()),
        );

        steady_error_path.add_successor(
            &SymbolicTransition::new(true_bdd.clone(), r_4.clone()),
            SteadyPath::new(vec![], idle_sym_state, sym_assignment),
        );

        steady_error_path
    }

    // initializes all smt variables and constraints of the test_automaton
    // for an abstract error path which applies r_0, r_1, r_3, r_2, r_4
    // needs to be called with get_test_automaton and get_test_abstract_path
    ///
    /// if initialized with get_test_abstract_path_one_step returns the encoder
    /// for the abstract error path which only applies r_0
    fn get_initialized_test_smt_encoder<'a>(
        aut: &'a IntervalThresholdAutomaton,
        path: &'a SteadyErrorPath,
    ) -> SMTEncoderSteady<'a> {
        let solver = SMTSolverBuilder::default();
        SMTEncoderSteady::new(solver, aut, path)
    }

    // initializes a steady error path for one step
    // that applies step transition r_0 and switches the interval for x from I_0 to I_1
    fn get_test_steady_error_path_one_step<'a>(
        aut: &'a IntervalThresholdAutomaton,
        error_graph: &'a ZCSErrorGraph,
    ) -> SteadyErrorPath<'a> {
        let full_state = error_graph.new_empty_sym_state().complement();
        let true_bdd = full_state.set_of_states();
        let idle_sym_state = ZCSStates::new(true_bdd.clone());

        let r_0 = aut.rules().find(|r| r.id() == 0).unwrap();

        // I = [0,1)
        let interval_0 = Interval::new(
            IntervalBoundary::from_const(0),
            false,
            IntervalBoundary::from_const(1),
            true,
        );

        // I = [1, n-t)
        let interval_1 = Interval::new(
            IntervalBoundary::from_const(1),
            false,
            IntervalBoundary::Bound(Threshold::new(
                [
                    (Parameter::new("n"), 1.into()),
                    (Parameter::new("t"), Fraction::new(1, 1, true)),
                ],
                0,
            )),
            true,
        );

        let intial_assignment = VariableAssignment::new_for_testing(HashMap::from([(
            Variable::new("x"),
            interval_0.clone(),
        )]));
        let sym_initial_assignment =
            SymbolicVariableAssignment::new(true_bdd.clone(), intial_assignment);
        let mut steady_error_path = SteadyErrorPath::new(
            SteadyPath::new(
                vec![&SymbolicTransition::new(true_bdd.clone(), r_0.clone())],
                idle_sym_state.clone(),
                sym_initial_assignment,
            ),
            error_graph,
        );

        let sym_assignment = SymbolicVariableAssignment::new(
            true_bdd.clone(),
            VariableAssignment::new_for_testing(HashMap::from([(
                Variable::new("x"),
                interval_1.clone(),
            )])),
        );
        steady_error_path.add_successor(
            &SymbolicTransition::new(true_bdd.clone(), r_0.clone()),
            SteadyPath::new(
                vec![&SymbolicTransition::new(true_bdd.clone(), r_0.clone())],
                idle_sym_state.clone(),
                sym_assignment.clone(),
            ),
        );

        steady_error_path
    }

    #[test]
    fn test_new_rule_counter() {
        let solver = SMTSolverBuilder::default();

        let r_0 = RuleBuilder::new(8, Location::new("l_0"), Location::new("l_1")).build();
        let r_1 = RuleBuilder::new(9, Location::new("l_1"), Location::new("l_0")).build();

        let aut = get_test_automaton();
        let error_graph = get_test_error_graph(&aut);
        let path = get_test_steady_error_path(&aut, &error_graph);
        let mut encoder = SMTEncoderSteady::new(solver, &aut, &path);

        let rules = vec![&r_0, &r_1, &r_0];
        encoder.rule_counter_to_smt.clear();
        encoder.initialize_rule_counters(rules.into_iter());

        let r_0_0 = encoder.rule_counter_to_smt[0].1;
        let r_1_1 = encoder.rule_counter_to_smt[1].1;
        let r_0_2 = encoder.rule_counter_to_smt[2].1;

        assert_eq!(
            format!("{}", encoder.ctx.smt_solver.display(r_0_0)),
            "rule_8_0"
        );
        assert_eq!(
            format!("{}", encoder.ctx.smt_solver.display(r_1_1)),
            "rule_9_1"
        );
        assert_eq!(
            format!("{}", encoder.ctx.smt_solver.display(r_0_2)),
            "rule_8_2"
        );
    }

    #[test]
    fn test_initialize_rule_counters() {
        let solver = SMTSolverBuilder::default();

        let r_0 = RuleBuilder::new(8, Location::new("l_0"), Location::new("l_1")).build();
        let r_1 = RuleBuilder::new(9, Location::new("l_1"), Location::new("l_0")).build();

        let aut = get_test_automaton();
        let error_graph = get_test_error_graph(&aut);
        let path = get_test_steady_error_path(&aut, &error_graph);
        let mut encoder = SMTEncoderSteady::new(solver, &aut, &path);

        let vec = vec![&r_0, &r_1, &r_0];

        encoder.rule_counter_to_smt.clear();

        encoder.initialize_rule_counters(vec.into_iter());

        assert_eq!(
            format!(
                "{}",
                encoder
                    .ctx
                    .smt_solver
                    .display(encoder.rule_counter_to_smt.first().unwrap().1)
            ),
            "rule_8_0"
        );
        assert_eq!(
            format!(
                "{}",
                encoder
                    .ctx
                    .smt_solver
                    .display(encoder.rule_counter_to_smt.get(1).unwrap().1)
            ),
            "rule_9_1"
        );
        assert_eq!(
            format!(
                "{}",
                encoder
                    .ctx
                    .smt_solver
                    .display(encoder.rule_counter_to_smt.get(2).unwrap().1)
            ),
            "rule_8_2"
        );
    }

    #[test]
    fn test_encode_step_transition() {
        let aut = get_test_automaton();
        let error_graph = get_test_error_graph(&aut);
        let path = get_test_steady_error_path(&aut, &error_graph);

        let encoder = get_initialized_test_smt_encoder(&aut, &path);
        // increment step transition
        let encoding = encoder.encode_step_transition(2, 1);

        let smt = format!("{}", encoder.ctx.smt_solver.display(encoding));

        assert!(smt.contains("(= rule_0_1 1)"));
        assert!(smt.contains("(= loc_l0_2 (- loc_l0_1 rule_0_1))"));
        assert!(smt.contains("(= loc_l1_2 (+ loc_l1_1 rule_0_1))"));
        assert!(smt.contains("(= loc_l2_2 loc_l2_1)"));
        assert!(smt.contains("(= var_x_2 (+ var_x_1 (* rule_0_1 1)))"));

        // decrement step transition
        let encoding = encoder.encode_step_transition(4, 3);

        let smt = format!("{}", encoder.ctx.smt_solver.display(encoding));
        assert!(smt.contains("(= rule_1_3 1)"));
        assert!(smt.contains("(= loc_l0_4 (- loc_l0_3 rule_1_3))"));
        assert!(smt.contains("(= loc_l1_4 (+ loc_l1_3 rule_1_3))"));
        assert!(smt.contains("(= loc_l2_4 loc_l2_3)"));
        assert!(smt.contains("(= var_x_4 (- var_x_3 (* rule_1_3 1)))"));

        // reset step transition
        let encoding = encoder.encode_step_transition(10, 8);

        let smt = format!("{}", encoder.ctx.smt_solver.display(encoding));
        assert!(smt.contains("(= rule_2_8 1)"));
        assert!(smt.contains("(= loc_l0_10 (- loc_l0_9 rule_2_8))"));
        assert!(smt.contains("(= loc_l1_10 (+ loc_l1_9 rule_2_8))"));
        assert!(smt.contains("(= loc_l2_10 loc_l2_9))"));
        assert!(smt.contains("(= var_x_10 0)"));
    }

    #[test]
    fn test_encode_update_shared_vars_inc() {
        let aut = get_test_automaton();
        let error_graph = get_test_error_graph(&aut);
        let path = get_test_steady_error_path(&aut, &error_graph);
        let encoder = SMTEncoderSteady::new(SMTSolverBuilder::default(), &aut, &path);
        let shared_smt = encoder.ctx.get_indexed_shared_smt(&Variable::new("x"), 1);
        let next_shared_smt = encoder.ctx.get_indexed_shared_smt(&Variable::new("x"), 2);
        let rule_smt = encoder.rule_counter_to_smt.get(1).unwrap().1;
        let encoding = encoder.encode_update_shared_var(
            &shared_smt,
            &next_shared_smt,
            rule_smt,
            &UpdateExpression::Inc(1),
        );

        let correct_encoding = "(= var_x_2 (+ var_x_1 (* rule_0_1 1)))";

        assert_eq!(
            format!("{}", encoder.ctx.smt_solver.display(encoding)),
            correct_encoding
        );
    }

    #[test]
    fn test_encode_update_shared_vars_dec() {
        let aut = get_test_automaton();
        let error_graph = get_test_error_graph(&aut);
        let path = get_test_steady_error_path(&aut, &error_graph);
        let encoder = SMTEncoderSteady::new(SMTSolverBuilder::default(), &aut, &path);
        let shared_smt = encoder.ctx.get_indexed_shared_smt(&Variable::new("x"), 1);
        let next_shared_smt = encoder.ctx.get_indexed_shared_smt(&Variable::new("x"), 2);
        let rule_smt = encoder.rule_counter_to_smt.get(1).unwrap().1;
        let encoding = encoder.encode_update_shared_var(
            &shared_smt,
            &next_shared_smt,
            rule_smt,
            &UpdateExpression::Dec(1),
        );

        let correct_encoding = "(= var_x_2 (- var_x_1 (* rule_0_1 1)))";

        assert_eq!(
            format!("{}", encoder.ctx.smt_solver.display(encoding)),
            correct_encoding
        );
    }

    #[test]
    fn test_encode_update_shared_vars_reset() {
        let aut = get_test_automaton();
        let error_graph = get_test_error_graph(&aut);
        let path = get_test_steady_error_path(&aut, &error_graph);
        let encoder = SMTEncoderSteady::new(SMTSolverBuilder::default(), &aut, &path);
        let shared_smt = encoder.ctx.get_indexed_shared_smt(&Variable::new("x"), 1);
        let next_shared_smt = encoder.ctx.get_indexed_shared_smt(&Variable::new("x"), 2);
        let rule_smt = encoder.rule_counter_to_smt.get(1).unwrap().1;
        let encoding = encoder.encode_update_shared_var(
            &shared_smt,
            &next_shared_smt,
            rule_smt,
            &UpdateExpression::Reset,
        );

        let correct_encoding = "(= var_x_2 0)";

        assert_eq!(
            format!("{}", encoder.ctx.smt_solver.display(encoding)),
            correct_encoding
        );
    }

    #[test]
    fn test_encode_update_shared_vars_unchanged() {
        let aut = get_test_automaton();
        let error_graph = get_test_error_graph(&aut);
        let path = get_test_steady_error_path(&aut, &error_graph);
        let encoder = SMTEncoderSteady::new(SMTSolverBuilder::default(), &aut, &path);
        let shared_smt = encoder.ctx.get_indexed_shared_smt(&Variable::new("x"), 1);
        let next_shared_smt = encoder.ctx.get_indexed_shared_smt(&Variable::new("x"), 2);
        let rule_smt = encoder.rule_counter_to_smt.get(1).unwrap().1;
        let encoding = encoder.encode_update_shared_var(
            &shared_smt,
            &next_shared_smt,
            rule_smt,
            &UpdateExpression::Unchanged,
        );

        let correct_encoding = "(= var_x_2 var_x_1)";

        assert_eq!(
            format!("{}", encoder.ctx.smt_solver.display(encoding)),
            correct_encoding
        );
    }

    #[test]
    fn test_encode_resilience_conditions() {
        let solver = SMTSolverBuilder::default();
        let aut = get_test_automaton();
        let error_graph = get_test_error_graph(&aut);
        let path = get_test_steady_error_path(&aut, &error_graph);
        let mut encoder = SMTEncoderSteady::new(solver, &aut, &path);

        let rc_1 = ParameterConstraint::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Parameter::new("n"))),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Const(3) * IntegerExpression::Param(Parameter::new("t"))),
        );

        let rc_2 = ParameterConstraint::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Parameter::new("t"))),
            ComparisonOp::Geq,
            Box::new(IntegerExpression::Param(Parameter::new("f"))),
        );
        let rcs = vec![&rc_1, &rc_2];

        let res = encoder.encode_resilience_conditions(rcs.into_iter());

        let correct_encoding = "(and (and true (> param_n (* 3 param_t))) (>= param_t param_f))";

        assert_eq!(
            format!("{}", encoder.ctx.smt_solver.display(res)),
            correct_encoding
        );
    }

    #[test]
    fn test_encode_loc_conditions() {
        let solver = SMTSolverBuilder::default();
        let aut = get_test_automaton();
        let error_graph = get_test_error_graph(&aut);
        let path = get_test_steady_error_path(&aut, &error_graph);
        let mut encoder = SMTEncoderSteady::new(solver, &aut, &path);

        let loc_constr_1 = LocationConstraint::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Location::new("l0"))),
            ComparisonOp::Eq,
            Box::new(
                IntegerExpression::Param(Parameter::new("n"))
                    - IntegerExpression::Param(Parameter::new("t")),
            ),
        );
        let loc_constr_2 = LocationConstraint::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Location::new("l1"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        );
        let loc_constr_3 = LocationConstraint::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Location::new("l2"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        );

        let init_loc_constrs = vec![&loc_constr_1, &loc_constr_2, &loc_constr_3];

        let res = encoder.encode_loc_conditions(init_loc_constrs.into_iter());

        let correct_encoding =
            "(and (and (and true (= loc_l0_0 (- param_n param_t))) (= loc_l1_0 0)) (= loc_l2_0 0))";

        assert_eq!(
            format!("{}", encoder.ctx.smt_solver.display(res)),
            correct_encoding
        );
    }

    #[test]
    fn test_encode_var_conditions() {
        let aut = get_test_automaton();
        let error_graph = get_test_error_graph(&aut);
        let path = get_test_steady_error_path(&aut, &error_graph);
        let mut encoder = SMTEncoderSteady::new(SMTSolverBuilder::default(), &aut, &path);

        let init_var_constr = BooleanVarConstraint::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Variable::new("x"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        );

        let res = encoder.encode_var_conditions(vec![&init_var_constr].into_iter());

        let correct_encoding = "(and true (= var_x_0 0))";

        assert_eq!(
            format!("{}", encoder.ctx.smt_solver.display(res)),
            correct_encoding
        );
    }

    #[test]
    fn test_encode_shared_interval_left_infty() {
        let aut = get_test_automaton();
        let error_graph = get_test_error_graph(&aut);
        let path = get_test_steady_error_path(&aut, &error_graph);
        let mut encoder = get_initialized_test_smt_encoder(&aut, &path);

        // I = (infty,infty)
        let interval = Interval::new(
            IntervalBoundary::new_infty(),
            true,
            IntervalBoundary::new_infty(),
            true,
        );
        encoder.ctx.set_curr_index(1);
        let res = encoder.encode_shared_interval(Variable::new("x"), interval);

        assert_eq!(format!("{}", encoder.ctx.smt_solver.display(res)), "false");
    }

    #[test]
    fn test_encode_shared_interval_right_infty() {
        let aut = get_test_automaton();
        let error_graph = get_test_error_graph(&aut);
        let path = get_test_steady_error_path(&aut, &error_graph);
        let mut encoder = get_initialized_test_smt_encoder(&aut, &path);

        // I = [n-t,infty)
        let interval = Interval::new(
            IntervalBoundary::Bound(Threshold::new(
                [
                    (Parameter::new("n"), 1.into()),
                    (Parameter::new("t"), Fraction::new(1, 1, true)),
                ],
                0,
            )),
            false,
            IntervalBoundary::new_infty(),
            true,
        );

        encoder.ctx.set_curr_index(1);
        let res = encoder.encode_shared_interval(Variable::new("x"), interval);

        assert_eq!(
            format!("{}", encoder.ctx.smt_solver.display(res)),
            "(and (>= var_x_1 (+ param_n (* (- 1) param_t))) true)"
        );
    }

    #[test]
    fn test_encode_shared_interval_interval_left_closed_right_closed() {
        let aut = get_test_automaton();
        let error_graph = get_test_error_graph(&aut);
        let path = get_test_steady_error_path(&aut, &error_graph);
        let mut encoder = get_initialized_test_smt_encoder(&aut, &path);

        // I = [0,n-t]
        let interval = Interval::new(
            IntervalBoundary::from_const(0),
            false,
            IntervalBoundary::Bound(Threshold::new(
                [
                    (Parameter::new("n"), 1.into()),
                    (Parameter::new("t"), Fraction::new(1, 1, true)),
                ],
                0,
            )),
            false,
        );

        encoder.ctx.set_curr_index(1);
        let res = encoder.encode_shared_interval(Variable::new("x"), interval);

        assert_eq!(
            format!("{}", encoder.ctx.smt_solver.display(res)),
            "(and (>= var_x_1 0) (<= var_x_1 (+ param_n (* (- 1) param_t))))"
        );
    }

    #[test]
    fn test_encode_shared_interval_interval_left_open_right_closed() {
        let aut = get_test_automaton();
        let error_graph = get_test_error_graph(&aut);
        let path = get_test_steady_error_path(&aut, &error_graph);
        let mut encoder = get_initialized_test_smt_encoder(&aut, &path);

        // I = (0,n-t]
        let interval = Interval::new(
            IntervalBoundary::from_const(0),
            true,
            IntervalBoundary::Bound(Threshold::new(
                [
                    (Parameter::new("n"), 1.into()),
                    (Parameter::new("t"), Fraction::new(1, 1, true)),
                ],
                0,
            )),
            false,
        );

        encoder.ctx.set_curr_index(1);
        let res = encoder.encode_shared_interval(Variable::new("x"), interval);

        assert_eq!(
            format!("{}", encoder.ctx.smt_solver.display(res)),
            "(and (> var_x_1 0) (<= var_x_1 (+ param_n (* (- 1) param_t))))"
        );
    }

    #[test]
    fn test_encode_shared_interval_interval_left_closed_right_open() {
        let aut = get_test_automaton();
        let error_graph = get_test_error_graph(&aut);
        let path = get_test_steady_error_path(&aut, &error_graph);
        let mut encoder = get_initialized_test_smt_encoder(&aut, &path);

        // I = [0,n-t)
        let interval = Interval::new(
            IntervalBoundary::from_const(0),
            false,
            IntervalBoundary::Bound(Threshold::new(
                [
                    (Parameter::new("n"), 1.into()),
                    (Parameter::new("t"), Fraction::new(1, 1, true)),
                ],
                0,
            )),
            true,
        );

        encoder.ctx.set_curr_index(1);
        let res = encoder.encode_shared_interval(Variable::new("x"), interval);

        assert_eq!(
            format!("{}", encoder.ctx.smt_solver.display(res)),
            "(and (>= var_x_1 0) (< var_x_1 (+ param_n (* (- 1) param_t))))"
        );
    }

    #[test]
    fn test_encode_shared_interval_interval_left_open_right_open() {
        let aut = get_test_automaton();
        let error_graph = get_test_error_graph(&aut);
        let path = get_test_steady_error_path(&aut, &error_graph);
        let mut encoder = get_initialized_test_smt_encoder(&aut, &path);

        // I = (0,n-t)
        let interval = Interval::new(
            IntervalBoundary::from_const(0),
            true,
            IntervalBoundary::Bound(Threshold::new(
                [
                    (Parameter::new("n"), 1.into()),
                    (Parameter::new("t"), Fraction::new(1, 1, true)),
                ],
                0,
            )),
            true,
        );

        encoder.ctx.set_curr_index(1);
        let res = encoder.encode_shared_interval(Variable::new("x"), interval);

        assert_eq!(
            format!("{}", encoder.ctx.smt_solver.display(res)),
            "(and (> var_x_1 0) (< var_x_1 (+ param_n (* (- 1) param_t))))"
        );
    }

    #[test]
    fn test_encode_abstract_path() {
        let aut = get_test_automaton();
        let error_graph = get_test_error_graph(&aut);
        let path = get_test_steady_error_path_one_step(&aut, &error_graph);
        let mut encoder = get_initialized_test_smt_encoder(&aut, &path);

        let res = encoder.encode_steady_error_path();

        assert_eq!(
            format!("{}", encoder.ctx.smt_solver.display(res)),
            "(and (and (and (and true (and (>= var_x_0 0) (< var_x_0 1))) (and (>= var_x_1 0) (< var_x_1 1))) (and (>= var_x_2 1) (< var_x_2 (+ param_n (* (- 1) param_t))))) (and (>= var_x_3 1) (< var_x_3 (+ param_n (* (- 1) param_t)))))"
        );
    }

    #[test]
    fn test_set_curr_index() {
        let aut = get_test_automaton();
        let error_graph = get_test_error_graph(&aut);
        let path = get_test_steady_error_path(&aut, &error_graph);
        let mut ctx = get_initialized_test_smt_encoder(&aut, &path).ctx;

        assert_eq!(ctx.curr_index, 0);

        ctx.set_curr_index(3);

        assert_eq!(ctx.curr_index, 3);
    }

    #[test]
    fn test_encode_step_processes_self_loop() {
        let solver = SMTSolverBuilder::default();

        let ta_builder =
            taco_threshold_automaton::general_threshold_automaton::builder::GeneralThresholdAutomatonBuilder::new("test")
                .with_locations(vec![Location::new("l0"), Location::new("l1"), Location::new("l2")])
                .unwrap()
                .initialize()
                .with_rules([RuleBuilder::new(0, Location::new("l0"), Location::new("l0")).build(), RuleBuilder::new(1, Location::new("l0"), Location::new("l1")).build(), RuleBuilder::new(2, Location::new("l0"), Location::new("l2")).build()])
                .unwrap();
        let ta = ta_builder.build();
        let lia =
            taco_threshold_automaton::lia_threshold_automaton::LIAThresholdAutomaton::try_from(
                ta.clone(),
            )
            .unwrap();

        let mut interval_tas = IntervalTABuilder::new(lia, SMTSolverBuilder::default(), vec![])
            .build()
            .unwrap();
        let ata = interval_tas.next().unwrap();

        let nxt = interval_tas.next();

        assert!(nxt.is_none(), "Got additional ta {}", nxt.unwrap());

        let error_graph = get_test_error_graph(&ata);
        let path = get_test_steady_error_path_one_step(&ata, &error_graph);

        let encoder = SMTEncoderSteady::new(solver, &ata, &path);

        let res = encoder.encode_step_transition(2, 1);

        let smt = format!("{}", encoder.ctx.smt_solver.display(res));
        assert!(smt.contains("(= rule_0_1 1)"));
        assert!(smt.contains("(= loc_l0_2 loc_l0_1))"));
        assert!(smt.contains("(= loc_l1_2 loc_l1_1))"));
        assert!(smt.contains("(= loc_l2_2 loc_l2_1))"));
    }

    #[test]
    fn test_encode_steady_path() {
        let aut = get_test_automaton();
        let error_graph = get_test_error_graph(&aut);
        let path = get_test_steady_error_path_one_step(&aut, &error_graph);
        let encoder = get_initialized_test_smt_encoder(&aut, &path);

        let res = encoder.encode_steady_path(0, 0, path.steady_paths().next().unwrap());

        let smt = format!("{}", encoder.ctx.smt_solver.display(res));

        assert!(smt.contains("(= loc_l2_1 loc_l2_0)"));
        assert!(smt.contains("(= loc_l0_1 (- loc_l0_0 rule_0_0))"));
        assert!(smt.contains("(= loc_l1_1 (+ loc_l1_0 rule_0_0))"));
        assert!(smt.contains("(= var_x_1 (+ var_x_0 (* rule_0_0 1)))"));
        assert!(smt.contains("(=> (> rule_0_0 0) (and (> rule_0_0 0) (> loc_l0_0 0)))"));
    }

    #[test]
    fn test_encode_steady_path_move_processes() {
        let aut = get_test_automaton();
        let error_graph = get_test_error_graph(&aut);
        let path = get_test_steady_error_path_one_step(&aut, &error_graph);
        let encoder = get_initialized_test_smt_encoder(&aut, &path);

        let res =
            encoder.encode_steady_path_move_processes(0, 0, path.steady_paths().next().unwrap());

        let smt = format!("{}", encoder.ctx.smt_solver.display(res));
        assert!(smt.contains("(= loc_l1_1 (+ loc_l1_0 rule_0_0))"));
        assert!(smt.contains("(= loc_l2_1 loc_l2_0)"));
        assert!(smt.contains("(= loc_l0_1 (- loc_l0_0 rule_0_0))"));
    }

    #[test]
    fn test_encode_steady_path_update_shared_variables() {
        let aut = get_test_automaton();
        let error_graph = get_test_error_graph(&aut);
        let path = get_test_steady_error_path_one_step(&aut, &error_graph);
        let encoder = get_initialized_test_smt_encoder(&aut, &path);

        let res = encoder.encode_steady_path_update_shared_variables(
            0,
            0,
            path.steady_paths().next().unwrap(),
        );

        assert_eq!(
            format!("{}", encoder.ctx.smt_solver.display(res)),
            "(and true (= var_x_1 (+ var_x_0 (* rule_0_0 1))))"
        );
    }

    #[test]
    fn test_abstract_is_non_spurious_without_spec() {
        let aut = get_test_automaton();
        let error_graph = get_test_error_graph(&aut);
        let path = get_test_steady_error_path_one_step(&aut, &error_graph);
        let mut encoder = get_initialized_test_smt_encoder(&aut, &path);

        let res = encoder.steady_is_non_spurious(None);

        assert!(res.is_non_spurious());
    }

    #[test]
    fn test_abstract_is_non_spurious_with_spec() {
        let aut = get_test_automaton();
        let error_graph = get_test_error_graph(&aut);
        let path = get_test_steady_error_path_one_step(&aut, &error_graph);
        let mut encoder = get_initialized_test_smt_encoder(&aut, &path);

        let res =
            encoder.steady_is_non_spurious(Some(&UpwardsClosedSet::new_cover(HashSet::from([
                Location::new("l1"),
                Location::new("l2"),
            ]))));
        assert!(!res.is_non_spurious());
    }

    #[test]
    fn test_extract_non_spurious_concrete_path_no_param_assignment() {
        let aut = get_test_automaton();
        let error_graph = get_test_error_graph(&aut);
        let path = get_test_steady_error_path_one_step(&aut, &error_graph);
        let mut smt_encoder = get_initialized_test_smt_encoder(&aut, &path);

        let res = smt_encoder.extract_non_spurious_concrete_path(SMTSolution::UNSAT);

        assert!(res.is_err());

        assert!(matches!(
            res.clone().unwrap_err(),
            SMTEncoderError::NoSatParamAssign(_),
        ));
    }

    #[test]
    fn test_extract_non_spurious_concrete_path() {
        let aut = get_test_automaton();
        let error_graph = get_test_error_graph(&aut);
        let path = get_test_steady_error_path_one_step(&aut, &error_graph);
        let mut smt_encoder = get_initialized_test_smt_encoder(&aut, &path);

        smt_encoder.steady_is_non_spurious(None);

        let res = smt_encoder.extract_non_spurious_concrete_path(SMTSolution::SAT);

        assert!(res.is_ok());

        let path = res.unwrap();

        assert!((path.parameter_values().count() != 0));
        assert!(path.get_parameter_value(&Parameter::new("n")).unwrap() > 0);

        assert_eq!(path.transitions().count(), 1);
        assert_eq!(path.transitions().next().unwrap().rule().id(), 0);

        assert_eq!(path.configurations().count(), 2);

        let configs = path.configurations().collect::<Vec<_>>();

        let conf_0 = configs.first().unwrap();
        let conf_1 = configs.get(1).unwrap();

        assert_eq!(conf_0.get_variable_value(&Variable::new("x")), 0);
        assert!(conf_1.get_variable_value(&Variable::new("x")) > 0);

        assert_eq!(conf_0.get_processes_in_location(&Location::new("l2")), 0);
        assert_eq!(conf_0.get_processes_in_location(&Location::new("l1")), 0);
        assert_eq!(conf_1.get_processes_in_location(&Location::new("l2")), 0);
        assert!(conf_1.get_processes_in_location(&Location::new("l1")) > 0);
        assert_eq!(
            conf_1.get_processes_in_location(&Location::new("l0")),
            conf_0.get_processes_in_location(&Location::new("l0"))
                - conf_1.get_processes_in_location(&Location::new("l1"))
        );
    }
}
