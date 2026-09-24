//! Error Graph
//!
//! This module contains the error graph construction based on the counter
//! system of a threshold automaton. The error graph is computed backwards from
//! the error states, until no new states are discovered.
//!
//! An error graph is said to be "empty" if it does not contain any initial
//! states, which implies that no error state is reachable from the initial
//! states.
//!
//! If the error graph is not empty, all possible paths need to be checked,
//! whether an actual non-spurious path exists. Such a path would be a counter
//! example to the property.
//!
//! The core logic for this exploration is implemented in the `node` module.

use std::{cell::RefCell, collections::VecDeque, rc::Rc};

use log::info;
use taco_model_checker::{ModelCheckerResult, internal_spec::upwards_closed_set::UpwardsClosedSet};
use taco_smt_encoder::SMTSolver;

use crate::{
    acs_threshold_automaton::{
        ACSThresholdAutomaton, configuration::partially_ordered_cfg_map::PartiallyOrderedConfigMap,
    },
    error_graph::{node::ErrorGraphNode, spurious_path_checker::SpuriousGraphChecker},
};

mod edge;
mod node;
mod spurious_path_checker;

/// Type alias for references to nodes in the error graph
///
/// The error graph is built using [`RefCell`], a type that implements the
/// internal mutability pattern. [`RefCell`] will check the borrow checker
/// constraints at runtime, therefore borrows must be done with care!
type NodeRef = Rc<RefCell<ErrorGraphNode>>;

impl From<ErrorGraphNode> for NodeRef {
    fn from(value: ErrorGraphNode) -> Self {
        Rc::new(RefCell::new(value))
    }
}

/// Error Graph storing all paths from initial abstract configurations to error
/// configurations
pub struct ErrorGraph {
    /// All nodes that have an initial configuration
    initial_leafs: Vec<NodeRef>,
    /// Threshold automaton for which the error graph has been constructed
    ta: ACSThresholdAutomaton,
    /// Specification for which the error graph has been constructed
    spec: UpwardsClosedSet,
}

impl ErrorGraph {
    /// Compute the error graph of the given specification
    ///
    /// Constructing the error graph can be a time and memory heavy operation.
    pub fn compute_error_graph(spec: UpwardsClosedSet, ta: ACSThresholdAutomaton) -> Self {
        // explore the error path
        let explored_cfgs = Self::construct_full_error_graph(&spec, &ta);

        // statistics
        let len_before_init = explored_cfgs.len();

        // Retain only nodes that are initial and their successors
        let initial_leafs: Vec<NodeRef> = explored_cfgs
            .get_all_values()
            .filter(|node| node.borrow().config().is_initial(&ta))
            .collect();

        let max_error_level = initial_leafs
            .iter()
            .map(|n| n.borrow().error_level())
            .max()
            .unwrap_or(0);

        info!(
            "Finished error graph construction for property '{}'. Explored {len_before_init} configurations of which {} are initial and have to be checked for spuriousness (max. error level {max_error_level})",
            spec,
            initial_leafs.len(),
        );

        Self {
            initial_leafs,
            ta,
            spec,
        }
    }

    /// Compute the full error graph for the [`ACSThresholdAutomaton`] and the
    /// given [`DisjunctionTargetConfig`]
    fn construct_full_error_graph(
        spec: &UpwardsClosedSet,
        ta: &ACSThresholdAutomaton,
    ) -> PartiallyOrderedConfigMap<NodeRef> {
        let mut explored_cfgs = ErrorGraphNode::new_roots_from_spec(spec, ta);
        let mut unexplored_queue = explored_cfgs.values().cloned().collect::<VecDeque<_>>();

        while let Some(unexplored) = unexplored_queue.pop_front() {
            ErrorGraphNode::compute_predecessors_and_insert_to_graph(
                &mut explored_cfgs,
                &mut unexplored_queue,
                &unexplored,
                ta,
            );
        }

        explored_cfgs
    }

    /// Check whether the error graph is empty, i.e. whether no counter example
    /// exists
    pub fn is_empty(&self) -> bool {
        self.initial_leafs.is_empty()
    }

    /// Check whether a non-spurious counter example exists
    ///
    /// This method might not terminate for threshold automata with resets
    pub fn check_for_non_spurious_counter_example(self, context: SMTSolver) -> ModelCheckerResult {
        let mut visitor = SpuriousGraphChecker::new(&self.ta, self.spec.clone(), context);

        visitor.find_violation(&self)
    }
}

#[cfg(test)]
mod tests {

    use taco_interval_ta::IntervalThresholdAutomaton;
    use taco_model_checker::{
        SpecificationTrait, TATrait,
        internal_spec::{ErrorSpec, ErrorTarget},
    };
    use taco_parser::{ParseTAWithLTL, bymc::ByMCParser};
    use taco_smt_encoder::SMTSolverBuilder;
    use taco_threshold_automaton::expressions::Location;

    use crate::{
        acs_threshold_automaton::{
            ACSThresholdAutomaton,
            configuration::{ACSIntervalState, ACSLocState, ACSTAConfig},
        },
        error_graph::ErrorGraph,
    };

    #[test]
    fn test_small_automaton_empty_err_graph() {
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
                        [](loc3 == 0)
                }
            }
          ";

        let (ta, spec) = ByMCParser::new().parse_ta_and_spec(test_spec).unwrap();
        let ctx = SMTSolverBuilder::default();

        let (spec, _) = ErrorSpec::try_from_eltl(spec.into_iter(), &ctx).unwrap();

        let spec_ta = ErrorSpec::transform_threshold_automaton(ta, spec, &ctx);

        assert_eq!(spec_ta.len(), 1);
        let (_, spec, ta) = spec_ta.into_iter().next().unwrap();

        let mut ta = IntervalThresholdAutomaton::try_from_general_ta(ta, &ctx, &spec)
            .expect("Failed to create interval ta");
        assert_eq!(ta.len(), 1, "Expected one interval automaton to be parsed");

        let ta = ACSThresholdAutomaton::from(ta.pop().unwrap());

        let ErrorTarget::Reach(spec) = spec else {
            panic!("Test case failed");
        };

        let e_graph = ErrorGraph::compute_error_graph(spec, ta);

        assert!(
            e_graph.is_empty(),
            "Got configs: {:?}",
            e_graph.initial_leafs
        );
    }

    #[test]
    fn test_small_automaton_chain_finds_init() {
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
                    loc4 : [3];
                    loc5 : [4];
                }

                inits (1) {
                    loc1 == n - f;
                    loc2 == 0;
                    loc3 == 0;
                    loc4 == 0;
                    loc5 == 0;
                    var1 == 0;
                    var2 == 0;
                    var3 == 0;
                }

                rules (4) {
                    0: loc1 -> loc2
                        when(true)
                        do {};
                    1: loc2 -> loc3
                        when(true)
                        do {};
                    2: loc3 -> loc4
                        when(true)
                        do {};
                    3: loc4 -> loc5
                        when(true)
                        do {};
                }

                specifications (1) {
                    test1:
                        [](loc5 == 0)
                }
            }
          ";

        let (ta, spec) = ByMCParser::new().parse_ta_and_spec(test_spec).unwrap();
        let ctx = SMTSolverBuilder::default();

        let (spec, _) = ErrorSpec::try_from_eltl(spec.into_iter(), &ctx).unwrap();

        let spec_ta = ErrorSpec::transform_threshold_automaton(ta, spec, &ctx);

        assert_eq!(spec_ta.len(), 1);
        let (_, spec, ta) = spec_ta.into_iter().next().unwrap();

        let mut ta = IntervalThresholdAutomaton::try_from_general_ta(ta, &ctx, &spec)
            .expect("Failed to create interval ta");
        assert_eq!(ta.len(), 1, "Expected one interval automaton to be parsed");

        let ta = ACSThresholdAutomaton::from(ta.pop().unwrap());

        let ErrorTarget::Reach(spec) = spec else {
            panic!("Test case failed");
        };

        let e_graph = ErrorGraph::compute_error_graph(spec, ta.clone());

        assert!(!e_graph.is_empty(),);

        let mut expected_loc_state = ACSLocState::new_empty(&ta);
        expected_loc_state[ta.to_cs_loc(&Location::new("loc1"))] = 1;
        let expected_interval_state = ACSIntervalState::new_mock_zero(&ta);
        let expected_config = ACSTAConfig::new_mock(expected_loc_state, expected_interval_state);

        assert!(
            e_graph
                .initial_leafs
                .into_iter()
                .any(|l| l.borrow().config() == &expected_config)
        );
    }
}
