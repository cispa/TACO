//! This module contains the symbolic error graph (ZCS error graph)
//! for a given property and a 01-CS (ZCS).

pub mod builder;

use log::info;

use std::collections::VecDeque;

use taco_interval_ta::IntervalTARule;
use taco_interval_ta::interval::Interval;
use taco_threshold_automaton::expressions::{Location, Variable};
use zcs::*;

use crate::paths::{SteadyErrorPath, SteadyPath, VariableAssignment};
use crate::smt_encoder_steady::SpuriousResult;
use crate::{ZCSModelCheckerContext, zcs};

/// Type representing a symbolic error graph (ZCS error graph)
#[derive(Debug, Clone)]
pub struct ZCSErrorGraph<'a> {
    /// set of error states
    error_states: ZCSStates,
    /// all iteratively explored states, these states contain bdd variables for transitions
    /// the first entry is equal to the error states
    explored_states: Vec<ZCSStates>,
    /// set of reached initial states of the error graph
    initial_states: ZCSStates,
    /// underlying 01-CS (ZCS)
    cs: ZCS<'a>,
}
impl ZCSErrorGraph<'_> {
    /// checks if an initial state has been reached
    pub fn is_empty(&self) -> bool {
        self.initial_states.is_empty()
    }

    /// reachable initial_states
    pub fn initial_states(&self) -> ZCSStates {
        self.initial_states.clone()
    }

    /// computes the set of successors reachable in the symbolic error graph (ZCS error graph) for a given symbolic transition
    pub fn compute_successors(&self, from: ZCSStates, with: SymbolicTransition) -> ZCSStates {
        // TODO: some possible optimization, i.e., check if transition id is contained in `from`
        let from = self.cs.abstract_rule_vars(from);
        let mut succ = self.cs.compute_successor(from, with.clone());
        //remove used transition id
        succ = self.cs.abstract_rule_vars(succ);
        //intersect with all states that are in the error graph
        let mut intersection = self.cs.new_empty_sym_state();
        for i in 0..self.explored_states.len() {
            intersection = intersection.union(&(self.explored_states[i].intersection(&succ)));
        }
        intersection
    }

    /// for set of states, it removes the error states
    /// additionally returns false, if the intersection is empty
    pub fn get_non_error_intersection(&self, states: ZCSStates) -> (bool, ZCSStates) {
        let intersection = self.explored_states[0].complement().intersection(&states);
        if !intersection.is_empty() {
            (true, intersection)
        } else {
            (false, intersection)
        }
    }

    /// computes the intersection of a set of states with the set of error states
    /// additionally returns, if the intersection is empty
    pub fn get_error_intersection(&self, states: ZCSStates) -> (bool, ZCSStates) {
        let intersection = self.error_states.intersection(&states);
        if !intersection.is_empty() {
            (true, intersection)
        } else {
            (false, intersection)
        }
    }

    /// returns the set of states where a given location is occupied
    pub fn get_sym_state_for_loc(&self, loc: &Location) -> ZCSStates {
        self.cs.get_sym_state_for_loc(loc)
    }

    /// returns the set of states where the given shared variable is in the given interval
    pub fn get_sym_state_for_shared_interval(
        &self,
        shared: &Variable,
        interval: &Interval,
    ) -> ZCSStates {
        self.cs.get_sym_state_for_shared_interval(shared, interval)
    }

    /// returns the set of states where the rule_id of a given rule is applied
    pub fn get_sym_state_for_rule(&self, rule: &IntervalTARule) -> ZCSStates {
        self.cs.get_sym_state_for_rule(rule)
    }

    /// returns an iterator over the encoded transition rules in the underlying 01-cs
    pub fn transitions(&self) -> impl Iterator<Item = &SymbolicTransition> {
        self.cs.transitions()
    }

    /// returns a new empty Symbolic State
    pub fn new_empty_sym_state(&self) -> ZCSStates {
        self.cs.new_empty_sym_state()
    }

    /// checks if the error graph contains a non-spurious error path
    /// `spurious_checker` is used to check if a path is spurious
    ///
    /// returns None if every path is spurious
    ///
    /// Note that this function is a semi-decision procedure
    /// if the underlying threshold automaton contains decrements or resets,
    /// i.e., it might not terminate.
    ///
    ///
    /// ```pseudo
    ///
    /// queue ← Queue::new()
    /// queue.push(SteadyPath::new(initial_states))
    /// while (queue ≠ ∅) {
    ///     steady_path ← queue.pop()
    ///     for rule in transitions {
    ///         successor_states ← compute_successors(steady_path.last_states, rule)
    ///         
    ///         // check if an error state can be reached
    ///         error_intersection ← get_error_intersection(successor_states)
    ///         if (error_intersection ≠ ∅) {
    ///             foreach assignment {
    ///                 if ((error_intersecion ∧ assignment) ≠ ∅) {
    ///                     updated_steady_path ← steady_path.add_successor(rule, error_intersection ∧ assignment)
    ///                     if updated_steady_path.is_non_spurious() {
    ///                         return "Found non spurious counter example"
    ///                     }  
    ///                 }
    ///             }
    ///         }
    ///
    ///         // check all other reachable steady paths which do not lead to an error state for spuriousness
    ///         non_error_intersection ← get_non_error_intersection(successor_states)
    ///         if (non_error_intersection ≠ ∅) {
    ///             foreach assignment {
    ///                 if ((non_error_intersection ∧ assignment) ≠ ∅) {
    ///                     // construct steady path for the given assignment
    ///                     successor_steady_path ← construct_steady_path(non_error_intersection ∧ assignment, assignment)
    ///                     updated_steady_path ← steady_path.add_successor(rule, successor_steady_path)
    ///                     if updated_steady_path.is_non_spurious() {
    ///                         queue.push(updated_steady_path)
    ///                     }
    ///                 }
    ///             }
    ///         }   
    ///     }
    /// }
    /// return "All error paths are spurious"
    /// ```
    pub fn contains_non_spurious_error_path(
        &self,
        smc_ctx: &ZCSModelCheckerContext,
    ) -> SpuriousResult {
        // all possible variable assignments
        let all_possible_assignments = self.get_all_possible_variable_assignments();

        // initial states that are already error states, i.e., error paths
        // without any transition
        let (non_empty, initial_error_states) = self.get_error_intersection(self.initial_states());
        if non_empty {
            for assignment in all_possible_assignments.iter() {
                if initial_error_states.contains_sym_assignment(assignment) {
                    let error_path = SteadyErrorPath::new(
                        SteadyPath::new(
                            vec![],
                            initial_error_states.intersect_assignment(assignment),
                            assignment.clone(),
                        ),
                        self,
                    );

                    let res = error_path.is_non_spurious(true, smc_ctx);
                    if res.is_non_spurious() {
                        return res;
                    }
                }
            }
        }

        // assignments that are reached except for error states
        let reachable_assignments = self.compute_reachable_variable_assignments();
        let mut queue: VecDeque<SteadyErrorPath> = VecDeque::new();
        for assignment in reachable_assignments.clone() {
            if self.initial_states().contains_sym_assignment(&assignment) {
                let initial_states_for_assignment =
                    self.initial_states.intersect_assignment(&assignment);
                let initial_steady_path =
                    self.construct_steady_path(initial_states_for_assignment, assignment);
                queue.push_back(SteadyErrorPath::new(initial_steady_path, self));
            }
        }

        // print spurious counter example from time to time
        // i.e., the first spurious ce, then the 10th, then the 100th, etc.
        let mut spurious_ce_count = 0;
        let mut next_to_print = 1;

        while !queue.is_empty() {
            let steady_error_path = queue.pop_front().unwrap();
            let last_states = steady_error_path.get_last_states();
            let last_assignment = steady_error_path.get_last_assignment();
            for rule in self.cs.transitions() {
                let successor_states = self.compute_successors(last_states.clone(), rule.clone());

                // check if an error state can be reached
                let (non_empty, error_intersection) =
                    self.get_error_intersection(successor_states.clone());
                if non_empty {
                    // check the possible variable assignments of the successor states
                    for assignment in all_possible_assignments.clone() {
                        if error_intersection.contains_sym_assignment(&assignment) {
                            let mut updated_steady_path = steady_error_path.clone();
                            let error_steady_path =
                                SteadyPath::new(vec![], error_intersection.clone(), assignment);
                            updated_steady_path.add_successor(rule, error_steady_path);

                            let res = updated_steady_path.is_non_spurious(true, smc_ctx);
                            if res.is_non_spurious() {
                                return res;
                            } else if smc_ctx.print_spurious_ce() {
                                info!("Spurious counterexample found: {updated_steady_path}");
                            }
                        }
                    }
                }
                // check all other reachable steady paths for non_spuriousness
                let (non_empty, mut non_error_intersection) =
                    self.get_non_error_intersection(successor_states.clone());
                if non_empty {
                    if smc_ctx.heuristics().is_monotonic()
                        || steady_error_path.last_is_monotonic(smc_ctx.ta())
                    {
                        non_error_intersection =
                            non_error_intersection.remove_assignment(&last_assignment);
                    }
                    if non_error_intersection.is_empty() {
                        continue;
                    }
                    for assignment in reachable_assignments.iter() {
                        if non_error_intersection.contains_sym_assignment(assignment) {
                            let mut updated_steady_path = steady_error_path.clone();
                            let non_error_states_for_assignment =
                                non_error_intersection.intersect_assignment(assignment);
                            let successor_steady_path = self.construct_steady_path(
                                non_error_states_for_assignment,
                                assignment.clone(),
                            );
                            updated_steady_path.add_successor(rule, successor_steady_path);
                            let res = updated_steady_path.is_non_spurious(false, smc_ctx);
                            if res.is_non_spurious() {
                                queue.push_back(updated_steady_path);
                            } else if smc_ctx.print_spurious_ce() {
                                spurious_ce_count += 1;
                                if spurious_ce_count == next_to_print {
                                    info!("Spurious subpath found: {updated_steady_path}");
                                    next_to_print *= 10;
                                }
                            }
                        }
                    }
                }
            }
        }
        // checked all possible paths, no non-spurious path found
        SpuriousResult::new_spurious()
    }

    /// returns all possible variable assignments
    fn get_all_possible_variable_assignments(&self) -> Vec<SymbolicVariableAssignment> {
        let mut possible_assignments = vec![VariableAssignment::new()];
        for shared in self.variables() {
            let mut updated_assignments = Vec::new();
            for assignment in possible_assignments {
                let intervals = self.get_ordered_intervals_for_shared(shared);
                for interval in intervals {
                    let mut updated_assignment = assignment.clone();
                    updated_assignment
                        .add_shared_var_interval(shared.clone(), interval.clone())
                        .expect("failed to update variable_assignment");
                    updated_assignments.push(updated_assignment);
                }
            }
            possible_assignments = updated_assignments;
        }

        possible_assignments
            .iter()
            .map(|assign| self.cs.get_sym_var_assignment(assign.clone()))
            .collect()
    }

    /// computes all reachable variable assignments of the error graph (except for error states)
    fn compute_reachable_variable_assignments(&self) -> Vec<SymbolicVariableAssignment> {
        let possible_assignments = self.get_all_possible_variable_assignments();

        possible_assignments
            .into_iter()
            .filter(|assign| {
                self.explored_states[1..self.explored_states.len()]
                    .iter()
                    .any(|state| state.contains_sym_assignment(assign))
            })
            .collect()
    }

    /// constructs the steady path for a given 'SymbolicState' and a 'SymbolicVariableAssignment'
    ///
    /// i.e., it computes all reachable states and possible transitions to stay in the same variable assignment
    ///
    /// Note that it only computes reachable states that are not an error state
    fn construct_steady_path(
        &self,
        sym_state: ZCSStates,
        assignment: SymbolicVariableAssignment,
    ) -> SteadyPath {
        let mut reachable_states = sym_state;
        let mut applied_rules = Vec::new();
        let mut reachable_states_changed = true;
        while reachable_states_changed {
            reachable_states_changed = false;
            for rule in self.cs.transitions() {
                let mut succ = self
                    .cs
                    .compute_successor(reachable_states.clone(), rule.clone());
                // remove all states that change the context
                succ = succ.intersect_assignment(&assignment);
                // remove all states that are not in the error graph
                let (not_empty, non_error_succ) = self.get_non_error_intersection(succ.clone());
                if not_empty {
                    if !applied_rules.contains(&rule) {
                        applied_rules.push(rule);
                    }
                    let updated_reachable_states = reachable_states.union(&non_error_succ);
                    if !updated_reachable_states.equal(&reachable_states) {
                        // we reached new states need to check all transitions again afterwards
                        reachable_states = updated_reachable_states;
                        reachable_states_changed = true;
                        break;
                    }
                }
            }
        }
        SteadyPath::new(applied_rules, reachable_states, assignment)
    }

    /// returns an iterator over the locations of the underlying threshold automaton
    pub fn locations(&self) -> impl Iterator<Item = &Location> {
        self.cs.locations()
    }

    /// returns an iterator over the shared variables of the underlying threshold automaton
    pub fn variables(&self) -> impl Iterator<Item = &Variable> {
        self.cs.variables()
    }

    /// returns an iterator over the ordered intervals for a given shared variable
    pub fn get_ordered_intervals_for_shared(&self, shared: &Variable) -> &Vec<Interval> {
        self.cs.get_ordered_intervals_for_shared(shared)
    }
}

#[cfg(test)]
mod tests {
    use crate::IntervalThresholdAutomaton;
    use crate::ZCSErrorGraphBuilder;
    use crate::zcs;
    use crate::zcs::ZCS;
    use crate::zcs::ZCSStates;
    use taco_interval_ta::IntervalTAAction;
    use taco_interval_ta::IntervalTARule;
    use taco_interval_ta::builder::IntervalTABuilder;
    use taco_interval_ta::interval::Interval;
    use taco_interval_ta::interval::IntervalBoundary;
    use taco_interval_ta::{IntervalActionEffect, IntervalConstraint};
    use taco_model_checker::ModelCheckerContext;
    use taco_model_checker::internal_spec::ErrorTarget;
    use taco_model_checker::internal_spec::upwards_closed_set::UpwardsClosedSet;
    use taco_smt_encoder::SMTSolverBuilder;
    use taco_threshold_automaton::ParameterConstraint;
    use taco_threshold_automaton::expressions::fraction::Fraction;
    use taco_threshold_automaton::lia_threshold_automaton::integer_thresholds::Threshold;

    use crate::ZCSModelCheckerContext;
    use crate::ZCSModelCheckerHeuristics;
    use taco_model_checker::SMTBddContext;

    use crate::zcs_error_graph::VariableAssignment;
    use taco_threshold_automaton::RuleDefinition;
    use taco_threshold_automaton::expressions::BooleanConnective;
    use taco_threshold_automaton::expressions::{Location, Variable};
    use taco_threshold_automaton::lia_threshold_automaton::integer_thresholds::WeightedSum;
    use taco_threshold_automaton::{
        BooleanVarConstraint, LocationConstraint,
        expressions::{ComparisonOp, IntegerExpression, Parameter},
        general_threshold_automaton::{Action, builder::RuleBuilder},
    };
    use zcs::builder::ZCSBuilder;

    /// Used to construct the SymbolicErrorGraph for the following threshold automaton:
    ///
    /// Threshold Automaton:
    /// Locations: {l0,l1,l2}
    /// Initial location: l0
    /// Parameter: {n,t}
    /// Shared Variables: x,y
    /// Initial location constraints: l0 = n - t & l1 = 0 & l2
    /// Rules:
    ///     r0: l0 -> l1, guard: true, action: x = x + 1
    ///     r1: l0 -> l2, guard: x >= n - t, action: none
    ///     r2: l1 -> l2, guard: x >= n - t, action: none
    ///
    /// Abstract Thershold Automaton:
    /// Intervals for x: I_0 = [0,1), I_1 = [1,n-t), I_2 = [n-t, infty)
    /// Interval Order: I_0 < I_1 < I_2
    /// Abstract Rules:
    ///     r0: l0 -> l1, guard: true, action: x = x + 1
    ///     r1: l0 -> l1, guard: x = I_2, action: none
    ///     r2: l1 -> l2, guard: x = I_2, action: none
    ///
    /// Structure of the symbolic 01-counter system:
    ///     [(1,0,0),I_0] --- r0 ---> [(-,1,0),{I_0,I_1}]
    ///     [(-,1,0),{I_0,I_1}] --- r0 ---> [(-,1,0),{I_0,I_1,I_2}]
    ///     [(-,1,0),{I_0,I_1,I_2}] --- r0 ---> [(-,1,0),{I_0,I_1,I_2}]
    ///     [(-,1,0),I_2] --- r1 ---> [(-,1,1),I_2]
    ///     [(-,1,0),I_2] --- r2 ---> [(-,-,1),I_2]
    ///
    /// The backwards reachability analysis for the set of error states {[(0,0,1),-]} looks as follows (already visited states are ignored):
    ///     level 1: [(0,0,1),-] <---- r1 ---- [(1,0,-),I_2],
    ///              [(0,0,1),-] <---- r2 ---- [(0,1,-),I_2]
    ///     level 2: [(1,0,-),I_2] <--- r2 --- [(1,1,-),I_2],
    ///              [(0,1,-),I_2] <--- r1 --- [(1,1,-),I_2],
    ///              [(0,1,-),I_1] <--- r0 --- [(1,-,-),{I_1,I_2}],
    ///     level 3: [(1,-,-),{I_1,I_2}] <--- r0 --- [(1,-,-),{I_0,I_1,I_2}]
    ///
    /// The symbol error graph for the set of error states {[(0,0,1),-]} looks as follows:
    ///     level 0: {[(0,0,1),-]}
    ///     level 1: {[(1,0,-),I_2]&r1, [(0,1,-),I_2]&r2} \cup {[(1,0,-),I_2]&r0]} (added in level 3)
    ///     level 2: {[(1,-,-),I_1]&r0), [(1,1,-),I_2] &(r0 | r1 | r2)} (&r1,r2 added in the next iteration)
    ///     level 3: {[(1,-,-),I_0]&r0}
    fn get_test_ata() -> IntervalThresholdAutomaton {
        let ta_builder =
            taco_threshold_automaton::general_threshold_automaton::builder::GeneralThresholdAutomatonBuilder::new("test")
                .with_locations(vec![
                    Location::new("l0"),
                    Location::new("l1"),
                    Location::new("l2"),
                ])
                .unwrap()
                .with_variables(vec![Variable::new("x"), Variable::new("y")])
                .unwrap()
                .with_parameters(vec![
                    Parameter::new("n"),
                    Parameter::new("t"),
                    Parameter::new("f"),
                ])
                .unwrap()
                .initialize()
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
                .with_resilience_conditions([ParameterConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Parameter::new("n")) - IntegerExpression::Atom(Parameter::new("t"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(1)),
                )])
                .unwrap()
                .with_initial_variable_constraints([BooleanVarConstraint::ComparisonExpression(Box::new(IntegerExpression::Atom(Variable::new("x"))), ComparisonOp::Eq, Box::new(IntegerExpression::Const(0))), BooleanVarConstraint::ComparisonExpression(Box::new(IntegerExpression::Atom(Variable::new("y"))), ComparisonOp::Eq, Box::new(IntegerExpression::Const(0)))])
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
                    RuleBuilder::new(1, Location::new("l0"), Location::new("l2"))
                        .with_guard(
                            BooleanVarConstraint::BinaryExpression(
                                Box::new(BooleanVarConstraint::ComparisonExpression(
                                    Box::new(IntegerExpression::Atom(Variable::new("x"))),
                                    ComparisonOp::Geq,
                                    Box::new(
                                        IntegerExpression::Param(Parameter::new("n"))
                                            - IntegerExpression::Param(Parameter::new("t")),
                                    ))),
                                    BooleanConnective::And,
                                    Box::new(BooleanVarConstraint::ComparisonExpression(
                                        Box::new(IntegerExpression::Atom(Variable::new("y"))),
                                        ComparisonOp::Eq,
                                        Box::new(IntegerExpression::Const(0)),
                                    )
                            )
                        ))
                        .build(),
                    RuleBuilder::new(2, Location::new("l1"), Location::new("l2"))
                    .with_guard(
                        BooleanVarConstraint::BinaryExpression(
                            Box::new(BooleanVarConstraint::ComparisonExpression(
                                Box::new(IntegerExpression::Atom(Variable::new("x"))),
                                ComparisonOp::Geq,
                                Box::new(
                                    IntegerExpression::Param(Parameter::new("n"))
                                        - IntegerExpression::Param(Parameter::new("t")),
                                ))),
                                BooleanConnective::And,
                                Box::new(BooleanVarConstraint::ComparisonExpression(
                                    Box::new(IntegerExpression::Atom(Variable::new("y"))),
                                    ComparisonOp::Eq,
                                    Box::new(IntegerExpression::Const(0)),
                                )
                        )
                        ))
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
        interval_tas.next().unwrap()
    }

    fn get_error_states(cs: &ZCS) -> ZCSStates {
        let l0 = cs.get_sym_state_for_loc(&Location::new("l0"));
        let l1 = cs.get_sym_state_for_loc(&Location::new("l1"));
        let l2 = cs.get_sym_state_for_loc(&Location::new("l2"));
        l0.complement()
            .intersection(&l1.complement())
            .intersection(&l2)
    }

    #[test]
    fn test_is_empty() {
        let ata = get_test_ata();
        let mgr = taco_bdd::BDDManager::default();
        let builder: ZCSBuilder = ZCSBuilder::new(&mgr, &ata);
        let cs = builder.build();
        let error_states = get_error_states(&cs);

        let error_graph_builder = ZCSErrorGraphBuilder::new(cs, error_states);
        let error_graph = error_graph_builder.build();

        assert!(!error_graph.is_empty());
    }

    #[test]
    fn test_initial_states() {
        let ata = get_test_ata();
        let mgr = taco_bdd::BDDManager::default();
        let builder: ZCSBuilder = ZCSBuilder::new(&mgr, &ata);
        let cs = builder.build();
        let error_states = get_error_states(&cs);

        let error_graph_builder = ZCSErrorGraphBuilder::new(cs, error_states);
        let error_graph = error_graph_builder.build();

        let l0 = error_graph.cs.get_sym_state_for_loc(&Location::new("l0"));
        let l1 = error_graph.cs.get_sym_state_for_loc(&Location::new("l1"));
        let l2 = error_graph.cs.get_sym_state_for_loc(&Location::new("l2"));

        // I_0 = [0,1)
        let interval_0 =
            Interval::new_constant(Fraction::new(0, 1, false), Fraction::new(1, 1, false));

        let i0 = error_graph
            .cs
            .get_sym_state_for_shared_interval(&Variable::new("x"), &interval_0);
        let i0 = i0.intersection(
            &error_graph
                .cs
                .get_sym_state_for_shared_interval(&Variable::new("y"), &interval_0),
        );
        // r0: l0 -> l1, guard: true, action: x = x + 1
        let abstract_rule_0 = IntervalTARule::new(
            0,
            Location::new("l0"),
            Location::new("l1"),
            IntervalConstraint::True,
            vec![IntervalTAAction::new(
                Variable::new("x"),
                IntervalActionEffect::Inc(1),
            )],
        );

        let r0 = error_graph.cs.get_sym_state_for_rule(&abstract_rule_0);

        let initial_states = l0
            .intersection(&l1.complement())
            .intersection(&l2.complement())
            .intersection(&i0)
            .intersection(&r0);

        assert!(initial_states.equal(&error_graph.initial_states()));
    }

    #[test]
    fn test_get_non_error_intersection_empty() {
        let ata = get_test_ata();
        let mgr = taco_bdd::BDDManager::default();
        let builder: ZCSBuilder = ZCSBuilder::new(&mgr, &ata);
        let cs = builder.build();
        let error_states = get_error_states(&cs);

        let error_graph_builder = ZCSErrorGraphBuilder::new(cs, error_states);
        let error_graph = error_graph_builder.build();

        let l0 = error_graph.cs.get_sym_state_for_loc(&Location::new("l0"));
        let l1 = error_graph.cs.get_sym_state_for_loc(&Location::new("l1"));
        let l2 = error_graph.cs.get_sym_state_for_loc(&Location::new("l2"));
        let error_states = l0
            .complement()
            .intersection(&l1.complement())
            .intersection(&l2);

        let res = error_graph.get_non_error_intersection(error_states);

        assert!(!res.0);
        assert!(res.1.is_empty());
    }

    #[test]
    fn test_get_non_error_intersection() {
        let ata = get_test_ata();
        let mgr = taco_bdd::BDDManager::default();
        let builder: ZCSBuilder = ZCSBuilder::new(&mgr, &ata);
        let cs = builder.build();
        let error_states = get_error_states(&cs);

        let error_graph_builder = ZCSErrorGraphBuilder::new(cs, error_states);
        let error_graph = error_graph_builder.build();

        let l0 = error_graph.cs.get_sym_state_for_loc(&Location::new("l0"));
        let l1 = error_graph.cs.get_sym_state_for_loc(&Location::new("l1"));
        let l2 = error_graph.cs.get_sym_state_for_loc(&Location::new("l2"));
        let error_states = l0
            .complement()
            .intersection(&l1.complement())
            .intersection(&l2);

        // I_0 = [0,1)
        let interval_0 =
            Interval::new_constant(Fraction::new(0, 1, false), Fraction::new(1, 1, false));

        let i0 = error_graph
            .cs
            .get_sym_state_for_shared_interval(&Variable::new("x"), &interval_0);

        let initial_states = l0
            .intersection(&l1.complement())
            .intersection(&l2.complement())
            .intersection(&i0);

        let res = error_graph.get_non_error_intersection(error_states.union(&initial_states));

        assert!(res.0);
        assert!(res.1.equal(&initial_states));
    }

    #[test]
    fn test_get_error_intersection_empty() {
        let ata = get_test_ata();
        let mgr = taco_bdd::BDDManager::default();
        let builder: ZCSBuilder = ZCSBuilder::new(&mgr, &ata);
        let cs = builder.build();
        let error_states = get_error_states(&cs);

        let error_graph_builder = ZCSErrorGraphBuilder::new(cs, error_states);
        let error_graph = error_graph_builder.build();

        let l0 = error_graph.cs.get_sym_state_for_loc(&Location::new("l0"));

        let res = error_graph.get_error_intersection(l0);

        assert!(!res.0);
        assert!(res.1.is_empty());
    }

    #[test]
    fn test_get_error_intersection() {
        let ata = get_test_ata();
        let mgr = taco_bdd::BDDManager::default();
        let builder: ZCSBuilder = ZCSBuilder::new(&mgr, &ata);
        let cs = builder.build();
        let error_states = get_error_states(&cs);

        let error_graph_builder = ZCSErrorGraphBuilder::new(cs, error_states);
        let error_graph = error_graph_builder.build();

        let l0 = error_graph.cs.get_sym_state_for_loc(&Location::new("l0"));
        let l1 = error_graph.cs.get_sym_state_for_loc(&Location::new("l1"));
        let l2 = error_graph.cs.get_sym_state_for_loc(&Location::new("l2"));

        // I_2 = [n-t,infty)
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

        let i2 = error_graph
            .cs
            .get_sym_state_for_shared_interval(&Variable::new("x"), &interval_2);

        let error_states = l0
            .complement()
            .intersection(&l1.complement())
            .intersection(&l2)
            .intersection(&i2);

        let builder = ZCSErrorGraphBuilder::new(error_graph.cs.clone(), error_states.clone());
        let error_graph = builder.build();

        // r0: l0 -> l1, guard: true, action: x = x + 1
        let abstract_rule_0 = IntervalTARule::new(
            0,
            Location::new("l0"),
            Location::new("l1"),
            IntervalConstraint::True,
            vec![IntervalTAAction::new(
                Variable::new("x"),
                IntervalActionEffect::Inc(1),
            )],
        );

        let r0 = error_graph.cs.get_sym_state_for_rule(&abstract_rule_0);

        let res = error_graph
            .get_error_intersection(l0.clone().union(&l2).intersection(&i2).intersection(&r0));

        assert!(res.0);
        assert!(
            res.1.equal(
                &l0.complement()
                    .intersection(&l1.complement())
                    .intersection(&l2)
                    .intersection(&i2)
                    .intersection(&r0)
            )
        );
    }

    #[test]
    fn test_contains_non_spurious_error_path() {
        let mgr = taco_bdd::BDDManager::default();
        let ata = get_test_ata();
        let builder: ZCSBuilder = ZCSBuilder::new(&mgr, &ata);
        let cs = builder.build();
        let error_states = get_error_states(&cs);

        let error_graph_builder = ZCSErrorGraphBuilder::new(cs, error_states);
        let sym_err_graph = error_graph_builder.build();

        let spec = ErrorTarget::Reach(UpwardsClosedSet::new_reach(
            [(Location::new("l2"), 1)],
            [Location::new("l0"), Location::new("l1")],
        ));

        let ctx = SMTBddContext::try_new(None).unwrap();

        let smc_ctx = ZCSModelCheckerContext::new(
            &ctx,
            ZCSModelCheckerHeuristics::DecrementAndIncrementHeuristics,
            &ata,
            &spec,
        );

        let res = sym_err_graph.contains_non_spurious_error_path(&smc_ctx);

        assert!(res.is_non_spurious());
    }

    #[test]
    fn test_get_sym_state_for_loc() {
        let ata = get_test_ata();
        let mgr = taco_bdd::BDDManager::default();
        let builder: ZCSBuilder = ZCSBuilder::new(&mgr, &ata);
        let cs = builder.build();
        let error_states = get_error_states(&cs);

        let error_graph_builder = ZCSErrorGraphBuilder::new(cs, error_states);
        let error_graph = error_graph_builder.build();

        let l0 = error_graph.cs.get_sym_state_for_loc(&Location::new("l0"));
        let l1 = error_graph.cs.get_sym_state_for_loc(&Location::new("l1"));
        let l2 = error_graph.cs.get_sym_state_for_loc(&Location::new("l2"));

        assert!(
            error_graph
                .get_sym_state_for_loc(&Location::new("l0"))
                .equal(&l0)
        );
        assert!(
            error_graph
                .get_sym_state_for_loc(&Location::new("l1"))
                .equal(&l1)
        );
        assert!(
            error_graph
                .get_sym_state_for_loc(&Location::new("l2"))
                .equal(&l2)
        );
    }

    #[test]
    fn test_get_sym_state_for_shared_interval() {
        let ata = get_test_ata();
        let mgr = taco_bdd::BDDManager::default();
        let builder: ZCSBuilder = ZCSBuilder::new(&mgr, &ata);
        let cs = builder.build();
        let error_states = get_error_states(&cs);

        let error_graph_builder = ZCSErrorGraphBuilder::new(cs, error_states);
        let error_graph = error_graph_builder.build();

        // I_0 = [0,1)
        let interval_0 =
            Interval::new_constant(Fraction::new(0, 1, false), Fraction::new(1, 1, false));
        let i0 = error_graph
            .cs
            .get_sym_state_for_shared_interval(&Variable::new("x"), &interval_0);

        assert!(
            error_graph
                .get_sym_state_for_shared_interval(&Variable::new("x"), &interval_0)
                .equal(&i0)
        );
    }

    #[test]
    fn test_get_sym_state_for_rule() {
        let ata = get_test_ata();
        let mgr = taco_bdd::BDDManager::default();
        let builder: ZCSBuilder = ZCSBuilder::new(&mgr, &ata);
        let cs = builder.build();
        let error_states = get_error_states(&cs);

        let error_graph_builder = ZCSErrorGraphBuilder::new(cs, error_states);
        let error_graph = error_graph_builder.build();

        // r0: l0 -> l1, guard: true, action: x = x + 1
        let abstract_rule_0 = IntervalTARule::new(
            0,
            Location::new("l0"),
            Location::new("l1"),
            IntervalConstraint::True,
            vec![IntervalTAAction::new(
                Variable::new("x"),
                IntervalActionEffect::Inc(1),
            )],
        );

        let r0 = error_graph.cs.get_sym_state_for_rule(&abstract_rule_0);

        assert!(
            error_graph
                .cs
                .get_sym_state_for_rule(&abstract_rule_0)
                .equal(&r0)
        );
    }

    #[test]
    fn test_transitions() {
        let ata = get_test_ata();
        let mgr = taco_bdd::BDDManager::default();
        let builder: ZCSBuilder = ZCSBuilder::new(&mgr, &ata);
        let cs = builder.build();
        let error_states = get_error_states(&cs);
        let error_graph_builder = ZCSErrorGraphBuilder::new(cs, error_states);
        let error_graph = error_graph_builder.build();

        let transitions = error_graph
            .transitions()
            .map(|r| r.abstract_rule().id())
            .collect::<Vec<_>>();
        assert_eq!(transitions.len(), 3);
        assert!(transitions.contains(&0));
        assert!(transitions.contains(&1));
        assert!(transitions.contains(&2));
    }

    #[test]
    fn test_new_empty_sym_state() {
        let ata = get_test_ata();
        let mgr = taco_bdd::BDDManager::default();
        let builder: ZCSBuilder = ZCSBuilder::new(&mgr, &ata);
        let cs = builder.build();
        let error_states = get_error_states(&cs);

        let error_graph_builder = ZCSErrorGraphBuilder::new(cs, error_states);
        let error_graph = error_graph_builder.build();

        let empty_state = error_graph.new_empty_sym_state();

        assert!(empty_state.is_empty());
    }

    #[test]
    fn test_compute_reachable_variable_assignments() {
        let ata = get_test_ata();
        let mgr = taco_bdd::BDDManager::default();
        let builder: ZCSBuilder = ZCSBuilder::new(&mgr, &ata);
        let cs = builder.build();
        let error_states = get_error_states(&cs);

        let error_graph_builder = ZCSErrorGraphBuilder::new(cs, error_states);
        let error_graph = error_graph_builder.build();

        let assignments = error_graph.compute_reachable_variable_assignments();

        // possible variable assignments are:
        // x = I_0
        // x = I_1
        // x = I_2
        assert_eq!(assignments.len(), 3);

        // I_0 = [0,1)
        let interval_0 =
            Interval::new_constant(Fraction::new(0, 1, false), Fraction::new(1, 1, false));

        // I_2 = [n-t,infty)
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
        let mut assign2 = VariableAssignment::new();
        assign2
            .add_shared_var_interval(Variable::new("x"), interval_2.clone())
            .unwrap();

        let mut reached_i_0 = false;
        let mut reached_i_1 = false;
        let mut reached_i_2 = false;
        for assign in assignments {
            for (var, interval) in assign.assignment().assignments() {
                if *var == Variable::new("y") {
                    assert_eq!(interval, &interval_0);
                }
                if *var == Variable::new("x") {
                    if interval == &interval_0 {
                        reached_i_0 = true;
                    } else if interval == &interval_2 {
                        reached_i_2 = true;
                    } else {
                        reached_i_1 = true;
                    }
                }
            }
        }
        assert!(reached_i_0);
        assert!(reached_i_1);
        assert!(reached_i_2);

        // I_1 = [1,\infty)
        let interval_1 = Interval::new(
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(1, 1, false)),
            false,
            IntervalBoundary::new_infty(),
            true,
        );

        let all_possible_assignments = error_graph.get_all_possible_variable_assignments();
        assert_eq!(all_possible_assignments.len(), 6);
        assert!(all_possible_assignments.iter().any(|assign| {
            assign
                .assignment()
                .assignments()
                .any(|(var, interval)| *var == Variable::new("y") && *interval == interval_1)
        }));
    }

    #[test]
    fn test_construct_steady_path() {
        let ata = get_test_ata();
        let mgr = taco_bdd::BDDManager::default();
        let builder: ZCSBuilder = ZCSBuilder::new(&mgr, &ata);
        let cs = builder.build();
        let error_states = get_error_states(&cs);

        let error_graph_builder = ZCSErrorGraphBuilder::new(cs, error_states);
        let error_graph = error_graph_builder.build();

        // I_0 = [0,1)
        let interval_0 =
            Interval::new_constant(Fraction::new(0, 1, false), Fraction::new(1, 1, false));
        let mut assignment = VariableAssignment::new();
        assignment
            .add_shared_var_interval(Variable::new("x"), interval_0.clone())
            .unwrap();
        assignment
            .add_shared_var_interval(Variable::new("y"), interval_0.clone())
            .unwrap();
        let assignment = error_graph.cs.get_sym_var_assignment(assignment);

        let initial_states = error_graph.initial_states();

        let steady_path =
            error_graph.construct_steady_path(initial_states.clone(), assignment.clone());

        println!("{:?}", steady_path._reachable_states());
        println!("{:?}", initial_states);

        assert!(steady_path._reachable_states().equal(&initial_states));
        assert!(
            steady_path
                ._reachable_states()
                .remove_assignment(&assignment)
                .is_empty()
        );
    }

    /// Used to construct the SymbolicErrorGraph for the following threshold automaton
    /// where cycles need to be unfolded to find a counterexample:
    ///
    /// Threshold Automaton:
    /// Locations: {l0,l1,l2,l3}
    /// Initial location: l0
    /// Parameter: {n}
    /// Shared Variables: x,y
    /// Initial location constraints: l0 = n & l1 = 0 & l2 = 0 & l3 = 0
    /// Rules:
    ///     r0: l0 -> l1, guard: x < 1, action: x = x + 1
    ///     r1: l1 -> l2, guard: true, action: none
    ///     r2: l2 -> l1, guard: true, action: y = y + 1
    ///     r3: l0 -> l3, guard: y >= 5, action: none
    fn get_test_cycle_ata() -> IntervalThresholdAutomaton {
        let ta_builder =
            taco_threshold_automaton::general_threshold_automaton::builder::GeneralThresholdAutomatonBuilder::new("test")
                .with_locations(vec![
                    Location::new("l0"),
                    Location::new("l1"),
                    Location::new("l2"),
                    Location::new("l3"),
                ])
                .unwrap()
                .with_variables(vec![Variable::new("x"), Variable::new("y")])
                .unwrap()
                .with_parameters(vec![
                    Parameter::new("n"),
                ])
                .unwrap()
                .initialize()
                .with_initial_location_constraints(vec![
                    LocationConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("l0"))),
                        ComparisonOp::Eq,
                        Box::new(
                            IntegerExpression::Param(Parameter::new("n"))
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
                    LocationConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("l3"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                ])
                .unwrap()
                .with_resilience_conditions([ParameterConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Parameter::new("n"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(1)),
                )])
                .unwrap()
                .with_initial_variable_constraints([BooleanVarConstraint::ComparisonExpression(Box::new(IntegerExpression::Atom(Variable::new("x"))), ComparisonOp::Eq, Box::new(IntegerExpression::Const(0))), BooleanVarConstraint::ComparisonExpression(Box::new(IntegerExpression::Atom(Variable::new("y"))), ComparisonOp::Eq, Box::new(IntegerExpression::Const(0)))])
                .unwrap()
                .with_rules(vec![
                    RuleBuilder::new(0, Location::new("l0"), Location::new("l1"))
                        .with_guard(
                            BooleanVarConstraint::ComparisonExpression(
                                Box::new(IntegerExpression::Atom(Variable::new("x"))),
                                ComparisonOp::Lt,
                                Box::new(IntegerExpression::Const(1)),
                            )
                        )
                        .with_action(
                            Action::new(
                                Variable::new("x"),
                                IntegerExpression::Atom(Variable::new("x"))
                                    + IntegerExpression::Const(1),
                            )
                            .unwrap(),
                        )
                        .build(),
                        RuleBuilder::new(1, Location::new("l1"), Location::new("l2"))
                        .build(),
                    RuleBuilder::new(2, Location::new("l2"), Location::new("l1"))
                    .with_action(
                        Action::new(
                            Variable::new("y"),
                            IntegerExpression::Atom(Variable::new("y"))
                                + IntegerExpression::Const(1),
                        )
                        .unwrap(),
                    )
                        .build(),
                    RuleBuilder::new(3, Location::new("l0"), Location::new("l3"))
                    .with_guard(
                        BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("y"))),
                            ComparisonOp::Geq,
                            Box::new(IntegerExpression::Const(5)),
                        )
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
        interval_tas.next().unwrap()
    }

    #[test]
    fn test_cycle_ta_for_spuriousness() {
        let ata = get_test_cycle_ata();
        let mgr = taco_bdd::BDDManager::default();
        let builder: ZCSBuilder = ZCSBuilder::new(&mgr, &ata);
        let cs = builder.build();
        let l3 = cs.get_sym_state_for_loc(&Location::new("l3"));
        // error states are those where l3 > 0
        let error_states = l3;

        let error_graph_builder = ZCSErrorGraphBuilder::new(cs, error_states);
        let sym_err_graph = error_graph_builder.build();

        let spec = ErrorTarget::Reach(UpwardsClosedSet::new_cover([Location::new("l3")]));

        let ctx = SMTBddContext::try_new(None).unwrap();
        let smc_ctx = ZCSModelCheckerContext::new(
            &ctx,
            ZCSModelCheckerHeuristics::DecrementAndIncrementHeuristics,
            &ata,
            &spec,
        );

        let res = sym_err_graph.contains_non_spurious_error_path(&smc_ctx);

        assert!(res.is_non_spurious());
    }
}
