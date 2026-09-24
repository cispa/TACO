//! This file contains the definitions of steady error paths
//! that are used in the symbolic model checker (ZCS model checker).

use std::collections::HashMap;
use std::fmt::Display;
use taco_interval_ta::IntervalThresholdAutomaton;
use taco_interval_ta::interval::Interval;
use taco_model_checker::internal_spec::ErrorTarget;
use taco_threshold_automaton::RuleDefinition;
use taco_threshold_automaton::expressions::Variable;
use taco_threshold_automaton::general_threshold_automaton::Rule;
use zcs::{SymbolicTransition, ZCSStates};

use crate::ZCSModelCheckerContext;
use crate::smt_encoder_steady::SMTEncoderSteady;
use crate::smt_encoder_steady::SpuriousResult;
use crate::zcs;
use crate::zcs::SymbolicVariableAssignment;
use crate::zcs_error_graph::ZCSErrorGraph;
use taco_threshold_automaton::ActionDefinition;
use taco_threshold_automaton::general_threshold_automaton::UpdateExpression;
use taco_threshold_automaton::general_threshold_automaton::UpdateExpression::{Dec, Inc};

/// Type that represents a steady error path
///
/// A steady error path consists of a sequence of steady paths π_0, ... , π_k
/// and a sequence of symbolic transitions r_0,...,r_{k-1}
/// where ∀ 0 < i \leq k: π_i is reached by applying rule r_{i-1} from π_{i-1}
#[derive(Debug, Clone)]
pub struct SteadyErrorPath<'a> {
    steady_paths: Vec<SteadyPath>,
    step_transitions: Vec<SymbolicTransition>,
    // underlying symbolic error graph
    error_graph: &'a ZCSErrorGraph<'a>,
}
impl<'a> SteadyErrorPath<'a> {
    /// creates a new Steady Error Path for a given SteadyPath
    pub fn new(steady_path: SteadyPath, error_graph: &'a ZCSErrorGraph) -> Self {
        SteadyErrorPath {
            steady_paths: vec![steady_path],
            step_transitions: Vec::new(),
            error_graph,
        }
    }
    /// returns the last SymbolicState of the last steady path
    pub fn get_last_states(&self) -> ZCSStates {
        self.steady_paths
            .last()
            .expect("the steady error path is empty")
            .reachable_states
            .clone()
    }
    /// returns the last SymbolicVariableAssignment of the last steady path
    pub fn get_last_assignment(&self) -> SymbolicVariableAssignment {
        self.steady_paths
            .last()
            .expect("the steady error path is empty")
            .variable_assignment
            .clone()
    }
    /// adds a new steady path to the steady error path that is reached with the given transition rule
    pub fn add_successor(&mut self, step_transition: &SymbolicTransition, steady_path: SteadyPath) {
        self.step_transitions.push(step_transition.clone());
        self.steady_paths.push(steady_path);
    }

    /// checks if the steady error path is non-spurious
    ///
    /// `reached_error_states` indicates if the last steady path reached an error state
    pub fn is_non_spurious(
        &self,
        reached_error_state: bool,
        smc_ctx: &ZCSModelCheckerContext,
    ) -> SpuriousResult {
        let mut smt_encoder = SMTEncoderSteady::new(
            smc_ctx.smt_bdd_context().smt_solver_builder().clone(),
            smc_ctx.ta(),
            self,
        );

        let ErrorTarget::Reach(spec) = smc_ctx.spec() else {
            todo!("Remove once implemented");
        };

        if reached_error_state {
            smt_encoder.steady_is_non_spurious(Some(spec))
        } else {
            smt_encoder.steady_is_non_spurious(None)
        }
    }

    /// returns the length of different contexts that is defined by the number of steady paths
    pub fn length_configurations(&self) -> u32 {
        self.steady_paths.len().try_into().unwrap()
    }
    /// returns an ordered iterator over all applied rules including the step rules
    pub fn concrete_rules_ordered(
        &self,
        ta: &'a IntervalThresholdAutomaton,
    ) -> impl Iterator<Item = &'a Rule> {
        let mut ordered_rule_vec = Vec::new();
        for i in 0..self.steady_paths.len() {
            let path = &self.steady_paths[i];
            for tr in &path.transitions {
                ordered_rule_vec.push(ta.get_derived_rule(tr.abstract_rule()));
            }
            // add step rule
            if i < self.steady_paths.len() - 1 {
                let step_rule = &self.step_transitions[i];
                ordered_rule_vec.push(ta.get_derived_rule(step_rule.abstract_rule()));
            }
        }
        ordered_rule_vec.into_iter()
    }

    /// returns an ordered iterator over the steady paths
    pub fn steady_paths(&self) -> impl Iterator<Item = &SteadyPath> {
        self.steady_paths.iter()
    }

    /// returns if the last steady error path is monotonic
    /// i.e., if for every shared variable the value is either only increasing or only decreasing
    pub fn last_is_monotonic(&self, ta: &IntervalThresholdAutomaton) -> bool {
        let last_steady_path = self
            .steady_paths
            .last()
            .expect("the steady error path is empty");
        for shared in self.error_graph.variables() {
            let mut inc_rules = false;
            let mut dec_rules = false;
            for rule in last_steady_path.transitions() {
                let rule = ta.get_derived_rule(rule.abstract_rule());
                let action_map = rule
                    .actions()
                    .map(|action| (action.variable(), action.update().clone()))
                    .collect::<HashMap<_, _>>();
                let update = action_map
                    .get(shared)
                    .unwrap_or(&UpdateExpression::Unchanged);
                match update {
                    Inc(_) => {
                        inc_rules = true;
                        if dec_rules {
                            return false;
                        }
                    }
                    Dec(_) => {
                        dec_rules = true;
                        if inc_rules {
                            return false;
                        }
                    }
                    UpdateExpression::Reset | UpdateExpression::Unchanged => {}
                }
            }
        }
        true
    }
}

impl Display for SteadyErrorPath<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "Symbolic Path with {} steady paths:",
            self.steady_paths.len(),
        )?;

        fn possible_locations(
            f: &mut std::fmt::Formatter<'_>,
            error_graph: &ZCSErrorGraph,
            sym_states: &ZCSStates,
        ) -> Result<(), Box<dyn std::error::Error>> {
            let mut uncovered_locations = Vec::new();
            let mut covered_locations = Vec::new();
            let mut both_locations = Vec::new();
            for loc in error_graph.locations() {
                let loc_sym_states = error_graph.get_sym_state_for_loc(loc);
                let covered = !sym_states.intersection(&loc_sym_states).is_empty();
                let uncovered = !sym_states
                    .intersection(&loc_sym_states.complement())
                    .is_empty();
                if covered && uncovered {
                    both_locations.push(loc);
                } else if covered {
                    covered_locations.push(loc.clone());
                } else if uncovered {
                    uncovered_locations.push(loc.clone());
                }
            }
            writeln!(f, "covered locations: {:?}", covered_locations)?;
            writeln!(f, "uncovered locations: {:?}", uncovered_locations)?;
            writeln!(
                f,
                "locations which can be covered or uncovered: {:?}",
                both_locations
            )?;
            Ok(())
        }

        let mut rule_index = 0;
        for steady_path in &self.steady_paths {
            writeln!(f, "Steady Path")?;

            let _ = possible_locations(f, self.error_graph, &steady_path.reachable_states);
            let rules = steady_path.transitions.clone();
            writeln!(
                f,
                "Possible rules: {:?}",
                rules
                    .iter()
                    .map(|r| "r_".to_owned() + &r.abstract_rule().id().to_string())
                    .collect::<Vec<String>>()
            )?;
            writeln!(
                f,
                "Variable Assignment:\n {}",
                steady_path.variable_assignment.assignment()
            )?;

            if rule_index < self.step_transitions.len() {
                writeln!(f, "        |",)?;
                writeln!(
                    f,
                    "        | reach new fragment by applying rule {}",
                    "r_".to_owned()
                        + &self.step_transitions[rule_index]
                            .abstract_rule()
                            .id()
                            .to_string()
                )?;
                writeln!(f, "        V")?;
                rule_index += 1;
            }
        }

        Ok(())
    }
}

/// Type that represents a steady path
///
/// A steady path describes a path fragment in which the context (variable) doesn't change
/// where `reachable_state` describes the set of symbolic states that can be reached within this path fragment
/// and `transitions` describes the set of transitions that can be applied.
#[derive(Debug, Clone)]
pub struct SteadyPath {
    transitions: Vec<SymbolicTransition>,
    reachable_states: ZCSStates,
    variable_assignment: SymbolicVariableAssignment,
}
impl SteadyPath {
    /// creates a new steady path for a given set of transitions, set of reachable states and a variable assignment
    pub fn new(
        transitions: Vec<&SymbolicTransition>,
        reachable_states: ZCSStates,
        variable_assignment: SymbolicVariableAssignment,
    ) -> Self {
        let mut transitions_without_duplicates = Vec::new();
        for tr in transitions {
            if !transitions_without_duplicates.contains(tr) {
                transitions_without_duplicates.push(tr.clone());
            }
        }
        SteadyPath {
            transitions: transitions_without_duplicates,
            reachable_states,
            variable_assignment,
        }
    }
    /// returns the length of the transitions inside the steady path
    pub fn length_transitions(&self) -> u32 {
        self.transitions.len().try_into().unwrap()
    }
    /// returns an iterator over the transitions
    pub fn transitions(&self) -> impl Iterator<Item = &SymbolicTransition> {
        self.transitions.iter()
    }
    /// returns the concrete variable assignment of the steady path
    pub fn variable_assignment(&self) -> &VariableAssignment {
        self.variable_assignment.assignment()
    }
    /// returns the reachable states of the steady path
    pub fn _reachable_states(&self) -> &ZCSStates {
        &self.reachable_states
    }
}

/// Type that represents a variable assignment
///
/// An variable assignment maps each shared variable to an interval
#[derive(Debug, Clone)]
pub struct VariableAssignment {
    assignment: HashMap<Variable, Interval>,
}
impl VariableAssignment {
    /// creates a new variable assignment
    pub fn new() -> Self {
        VariableAssignment {
            assignment: HashMap::new(),
        }
    }

    /// this function is only used for generating tests in smt_encoder
    pub fn new_for_testing(assignment: HashMap<Variable, Interval>) -> Self {
        VariableAssignment { assignment }
    }

    /// add a new assignment for the given shared variable with the given interval
    /// returns an error if there already exists an entry for Variable `shared`
    pub fn add_shared_var_interval(
        &mut self,
        shared: Variable,
        interval: Interval,
    ) -> Result<(), VariableAssignmentError> {
        if self.assignment.contains_key(&shared) {
            return Err(VariableAssignmentError::VariableAlreadyAssigned(shared));
        }
        self.assignment.insert(shared, interval);
        Ok(())
    }
    /// iterator over interval assignments for each shared variable
    pub fn assignments(&self) -> impl Iterator<Item = (&Variable, &Interval)> {
        self.assignment.iter()
    }
}
impl Default for VariableAssignment {
    fn default() -> Self {
        Self::new()
    }
}
impl Display for VariableAssignment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (shared, interval) in self.assignment.iter() {
            writeln!(f, "    {shared}: {interval}")?;
        }
        Ok(())
    }
}

/// Custom Error type to indicate an error
/// when operating on a VariableAssignment
#[derive(Debug, Clone)]
pub enum VariableAssignmentError {
    /// Error indicating that there already exists entry for this shared variable
    VariableAlreadyAssigned(Variable),
}

impl std::error::Error for VariableAssignmentError {}

impl Display for VariableAssignmentError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VariableAssignmentError::VariableAlreadyAssigned(shared) => {
                write!(
                    f,
                    "There already exists an entry for the shared variable {shared}"
                )
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use super::VariableAssignment;
    use crate::paths::VariableAssignmentError;
    use crate::zcs::ZCS;
    use crate::zcs::ZCSStates;
    use std::vec;
    use taco_interval_ta::IntervalThresholdAutomaton;
    use taco_interval_ta::builder::IntervalTABuilder;
    use taco_interval_ta::interval::Interval;
    use taco_interval_ta::interval::IntervalBoundary;
    use taco_smt_encoder::SMTSolverBuilder;
    use taco_threshold_automaton::BooleanVarConstraint;
    use taco_threshold_automaton::LocationConstraint;
    use taco_threshold_automaton::ParameterConstraint;
    use taco_threshold_automaton::expressions::ComparisonOp;
    use taco_threshold_automaton::expressions::IntegerExpression;
    use taco_threshold_automaton::expressions::{Location, Parameter, Variable};
    use taco_threshold_automaton::general_threshold_automaton::Action;
    use taco_threshold_automaton::general_threshold_automaton::builder::RuleBuilder;

    /// returns the underlying threshold automaton for these test cases
    ///
    ///  /// Threshold Automaton:
    /// Locations: {l0,l1,l2}
    /// Initial location: l0
    /// Parameter: {n,t}
    /// Shared Variable: x
    /// Initial location constraints: l0 = n - t & l1 = 0 & l2 = 0
    /// Rules:
    ///     r0: l0 -> l1, guard: true, action: x = x + 1
    ///     r1: l0 -> l2, guard: x >= n - t, action: none
    ///     r2: l1 -> l2, guard: x >= n - t, action: none
    ///
    /// Abstract Threshold Automaton:
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
    /// The symbolic error graph for the set of error states {[(0,0,1),-]} looks as follows:
    ///     level 0: {[(0,0,1),-]}
    ///     level 1: {[(1,0,-),I_2]&r1, [(0,1,-),I_2]&r2} \cup {[(1,0,-),I_2]&r0]} (added in level 3)
    ///     level 2: {[(1,-,-),I_1]&r0), [(1,1,-),I_2] &(r0 | r1 | r2)} (&r1,r2 added in the next iteration)
    ///     level 3: {[(1,-,-),I_0]&r0}
    fn _get_ata() -> IntervalThresholdAutomaton {
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
                .with_resilience_conditions([ParameterConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Parameter::new("n")) - IntegerExpression::Atom(Parameter::new("t"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(1)),
                )])
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
                .with_initial_variable_constraints(vec![
                    BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("x"))),
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
                    RuleBuilder::new(1, Location::new("l0"), Location::new("l2"))
                        .with_guard(BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("x"))),
                            ComparisonOp::Geq,
                            Box::new(
                                IntegerExpression::Param(Parameter::new("n"))
                                    - IntegerExpression::Param(Parameter::new("t")),
                            ),
                        ))
                        .build(),
                    RuleBuilder::new(2, Location::new("l1"), Location::new("l2"))
                        .with_guard(BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("x"))),
                            ComparisonOp::Geq,
                            Box::new(
                                IntegerExpression::Param(Parameter::new("n"))
                                    - IntegerExpression::Param(Parameter::new("t")),
                            ),
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
        let ata = interval_tas.next().unwrap();

        let nxt = interval_tas.next();
        assert!(nxt.is_none(), "Got additional ta {}", nxt.unwrap());

        ata
    }

    /// returns the set of error states for these test cases
    fn _get_error_states(cs: &ZCS) -> ZCSStates {
        let l0 = cs.get_sym_state_for_loc(&Location::new("l0"));
        let l1 = cs.get_sym_state_for_loc(&Location::new("l1"));
        let l2 = cs.get_sym_state_for_loc(&Location::new("l2"));
        l0.complement()
            .intersection(&l1.complement())
            .intersection(&l2)
    }

    #[test]
    fn test_variable_assignment() {
        let mut var_assignment = VariableAssignment::new();

        let test_interval = Interval::new(
            IntervalBoundary::new_infty(),
            true,
            IntervalBoundary::new_infty(),
            true,
        );

        let mut res =
            var_assignment.add_shared_var_interval(Variable::new("x"), test_interval.clone());

        assert!(res.is_ok());

        assert!(var_assignment.assignment.contains_key(&Variable::new("x")));
        assert_eq!(var_assignment.assignment.len(), 1);

        let cloned_assign = var_assignment.clone();
        let mut assign_it = cloned_assign.assignments();

        let mut next = assign_it.next();

        assert!(next.is_some());
        assert_eq!(*next.unwrap().0, Variable::new("x"));

        next = assign_it.next();

        assert!(next.is_none());

        res = var_assignment.add_shared_var_interval(Variable::new("x"), test_interval);

        assert!(res.is_err());

        assert!(matches!(
            res.clone().unwrap_err(),
            VariableAssignmentError::VariableAlreadyAssigned(_)
        ));
    }

    /// Construct the following threshold automaton for these test cases:
    ///
    /// Threshold Automaton:
    /// Locations: {l0,l1,l2}
    /// Initial location: l0
    /// Parameter: {n,t}
    /// Shared Variable: x, y(dummy variable)
    /// Initial location constraints: l0 = n - t & l1 = 0 & l2 = 0
    /// Rules:
    ///     r0: l0 -> l1, guard: true, action: x = x + 1
    ///     r1: l0 -> l2, guard: x >= n - t, action: none
    ///     r2: l1 -> l2, guard: x >= n - t, action: none
    ///
    /// Abstract Threshold Automaton:
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
    /// The symbolic error graph for the set of error states {[(-,-,1),-]} looks as follows:
    ///     level 0: {[(-,-,1),-]}
    ///     level 1: {[(1,0,-),I_2]&r1, [(0,1,-),I_2]&r2} \cup {[(1,0,-),I_2]&r0]} (added in level 3)
    ///     level 2: {[(1,-,-),I_1]&r0), [(1,1,-),I_2] &(r0 | r1 | r2)} (&r1,r2 added in the next iteration)
    ///     level 3: {[(1,-,-),I_0]&r0}
    fn _get_ata_for_spurious_checking() -> IntervalThresholdAutomaton {
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
                .with_initial_variable_constraints(vec![BooleanVarConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("x"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )])
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
                        .with_guard(BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("x"))),
                            ComparisonOp::Geq,
                            Box::new(
                                IntegerExpression::Param(Parameter::new("n"))
                                    - IntegerExpression::Param(Parameter::new("t")),
                            ),
                        ))
                        .build(),
                    RuleBuilder::new(2, Location::new("l1"), Location::new("l2"))
                        .with_guard(BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("x"))),
                            ComparisonOp::Geq,
                            Box::new(
                                IntegerExpression::Param(Parameter::new("n"))
                                    - IntegerExpression::Param(Parameter::new("t")),
                            ),
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
        let ata = interval_tas.next().unwrap();

        let nxt = interval_tas.next();
        assert!(nxt.is_none(), "Got additional ta {}", nxt.unwrap());

        ata
    }

    /// constructs the error states for these test cases
    fn _get_error_states_for_spurious_checking(cs: &ZCS) -> ZCSStates {
        cs.get_sym_state_for_loc(&Location::new("l2"))
    }
}
