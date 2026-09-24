//! Node type of the error graph

use std::collections::VecDeque;

use log::{debug, info};
use taco_model_checker::internal_spec::upwards_closed_set::UpwardsClosedSet;

use crate::{
    acs_threshold_automaton::{
        ACSThresholdAutomaton,
        configuration::{ACSTAConfig, partially_ordered_cfg_map::PartiallyOrderedConfigMap},
    },
    error_graph::{NodeRef, edge::ErrorGraphEdge},
};

/// Node in the error graph
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ErrorGraphNode {
    /// Distance to an error configuration
    error_level: usize,
    /// Configuration
    config: ACSTAConfig,
    /// Parent nodes
    /// [`ErrorGraphEdge`]s to nodes with a smaller distance to an error
    parents: Vec<ErrorGraphEdge>,
    /// Rules that result in a self-loop
    self_loops: Vec<u32>,
    /// [`ErrorGraphEdge`]s to a equal or higher error level node, potentially
    /// part of a cycle
    back_edges: Vec<ErrorGraphEdge>,
}

impl ErrorGraphNode {
    /// Get the error graph edges leading to the parents of the current node
    ///
    /// The edges returned here will have an error level smaller than the current
    /// node
    pub fn parents(&self) -> impl Iterator<Item = &ErrorGraphEdge> {
        self.parents.iter()
    }

    /// Get all rules that can be self-loops
    pub fn self_loops(&self) -> impl Iterator<Item = &u32> {
        self.self_loops.iter()
    }

    /// Get rules that can lead to higher or equal error level
    pub fn back_edges(&self) -> impl Iterator<Item = &ErrorGraphEdge> {
        self.back_edges.iter()
    }

    /// Get the configuration of the current node
    pub fn config(&self) -> &ACSTAConfig {
        &self.config
    }

    /// Get the error level of the current node
    pub fn error_level(&self) -> usize {
        self.error_level
    }

    /// Create new root error nodes from the specification
    ///
    /// Note: This function only returns the root of the error graph, to
    /// construct the full graph
    /// [`ErrorGraphNode::compute_predecessors_and_insert_to_graph`]
    /// for all computed nodes until the `to_explore_queue` is empty
    pub fn new_roots_from_spec(
        spec: &UpwardsClosedSet,
        ta: &ACSThresholdAutomaton,
    ) -> PartiallyOrderedConfigMap<NodeRef> {
        let error_level = 0;

        let configs = ACSTAConfig::from_disjunct_target(spec, ta);

        let mut res: PartiallyOrderedConfigMap<NodeRef> = PartiallyOrderedConfigMap::new();

        configs
            .into_iter()
            .map(|config| {
                let node: NodeRef = Self {
                    error_level,
                    config: config.clone(),
                    self_loops: Vec::new(),
                    parents: Vec::new(),
                    back_edges: Vec::new(),
                }
                .into();

                (config, node)
            })
            .for_each(|(config, node)| {
                let (smaller, bigger) = res.get_leq_or_bigger(&config);

                if smaller.is_some() {
                    return;
                }

                if let Some(bigger_cfg) = bigger {
                    let bigger_cfg = bigger_cfg.borrow().config().clone();
                    res.remove_entries_with_config(&bigger_cfg);
                }

                res.insert(config, node);
            });

        debug_assert!(res.len() >= 1);
        info!("Found {} potentially reachable error configs", res.len());

        res
    }

    /// Compute the predecessor of `node_to_compute_succs` in `ta`, adding nodes
    /// that still require exploration to `to_explore_queue` while checking that
    /// no smaller or equal node exists in `cfg_node_map`
    ///
    /// This function corresponds to `ComputePredBasis` of Algorithm 1 in the
    /// paper
    ///
    /// Safety: This function assumes that none of the nodes in the error graph
    /// still have an existing borrow
    pub fn compute_predecessors_and_insert_to_graph(
        cfg_node_map: &mut PartiallyOrderedConfigMap<NodeRef>,
        to_explore_queue: &mut VecDeque<NodeRef>,
        node_to_explore: &NodeRef,
        ta: &ACSThresholdAutomaton,
    ) {
        // clone the values and drop the borrow
        let error_level = node_to_explore.borrow().error_level + 1;
        let config_node_to_explore = node_to_explore.borrow().config.clone();

        // compute all predecessors from all rules
        for rule in ta.rules() {
            let predecessors = config_node_to_explore.compute_potential_predecessors(rule, ta);
            if predecessors.is_none() {
                continue;
            }
            let predecessors = predecessors.unwrap();

            for cfg in predecessors {
                if cfg == config_node_to_explore {
                    // Should be the only existing borrow (for the whole graph)
                    node_to_explore.borrow_mut().self_loops.push(rule.id());
                    continue;
                }

                // New edge to insert
                let new_edge = ErrorGraphEdge::new(rule, node_to_explore.clone());

                let (smaller_or_eq_node, bigger_node) = cfg_node_map.get_leq_or_bigger(&cfg);

                // If there exists a smaller or equal node in the graph, insert
                // the new edge accordingly
                if let Some(small_or_eq_node) = smaller_or_eq_node {
                    Self::insert_existing_smaller_node(
                        small_or_eq_node,
                        node_to_explore,
                        new_edge.clone(),
                        rule.id(),
                    );
                    continue;
                }

                // If there exists a bigger node in the graph, remove it but keep edges
                if let Some(bigger_node) = bigger_node {
                    let bigger_node = bigger_node.clone();
                    let bigger_node_cfg = bigger_node.borrow().config().clone();

                    debug_assert!(
                        bigger_node_cfg != cfg,
                        "Equal configurations should have been caught beforehand: bigger {}, cfg {}",
                        bigger_node_cfg.display_compact(ta),
                        cfg.display_compact(ta)
                    );

                    Self::insert_existing_bigger_node(&bigger_node, cfg.clone(), new_edge);

                    // remove the index by the bigger node
                    cfg_node_map.remove_entries_with_config(&bigger_node_cfg);

                    // continue exploring the smaller node
                    to_explore_queue.push_back(bigger_node.clone());
                    // reindex node by its new config
                    cfg_node_map.insert(cfg, bigger_node);
                    continue;
                }

                // Node is incomparable or smaller than all existing ones,
                // we need to insert and explore it
                let node = Self {
                    error_level,
                    config: cfg.clone(),
                    parents: vec![new_edge],
                    self_loops: vec![],
                    back_edges: vec![],
                };

                debug!("Found new node {}", node.config.display_compact(ta));
                let node: NodeRef = node.into();

                cfg_node_map.insert(cfg, node.clone());
                to_explore_queue.push_back(node);
            }
        }
    }

    /// Insert the new configuration and corresponding edge into the error graph,
    /// in case there exists an already inserted node with a smaller or equal
    /// configuration
    ///
    /// This function corresponds to line 20-21 in Algorithm 1
    fn insert_existing_smaller_node(
        smaller_or_eq_node: &NodeRef,
        node_to_explore: &NodeRef,
        edge_to_insert: ErrorGraphEdge,
        rule_id: u32,
    ) {
        // Check whether we are in a self-loop, if this is the case
        // simply insert the rule as such
        if smaller_or_eq_node == node_to_explore {
            // Should be the only existing borrow (for the whole graph)
            smaller_or_eq_node.borrow_mut().self_loops.push(rule_id);
            return;
        }

        let error_level = node_to_explore.borrow().error_level();

        // `eq_node` is on the same error level (or a bigger one),
        // therefore `node_to_explore` must be a parent
        // to `eq_node`
        if smaller_or_eq_node.borrow().error_level >= error_level {
            // This should not happen as long as `to_explore_queue`
            // is a FIFO queue
            ErrorGraphEdge::insert_to_edge_collection(
                &mut smaller_or_eq_node.borrow_mut().parents,
                edge_to_insert,
            );
            return;
        }

        // `smaller_or_eq_node` is from a smaller error level, therefore
        // we are on a back edge with the potential for cycles
        ErrorGraphEdge::insert_to_edge_collection(
            &mut smaller_or_eq_node.borrow_mut().back_edges,
            edge_to_insert,
        );
    }

    /// Insert the new configuration and corresponding edge into the error graph,
    /// in case there exists an already inserted node with a bigger
    /// configuration
    ///
    /// This function corresponds to line 24-26 in Algorithm 1
    fn insert_existing_bigger_node(
        bigger_node: &NodeRef,
        cfg_to_insert: ACSTAConfig,
        edge_to_insert: ErrorGraphEdge,
    ) {
        if bigger_node == edge_to_insert.node() {
            bigger_node
                .borrow_mut()
                .self_loops
                .extend(edge_to_insert.get_ids_of_rules());

            bigger_node.borrow_mut().config = cfg_to_insert;
            return;
        }

        let mut bigger_node = bigger_node.borrow_mut();
        // replace the configuration
        bigger_node.config = cfg_to_insert;

        ErrorGraphEdge::insert_to_edge_collection(&mut bigger_node.back_edges, edge_to_insert);
    }
}

#[cfg(test)]
mod mock_objects {
    use crate::{
        acs_threshold_automaton::configuration::ACSTAConfig,
        error_graph::{edge::ErrorGraphEdge, node::ErrorGraphNode},
    };

    impl ErrorGraphNode {
        /// Create a new mock error graph node
        pub fn new_mock(
            error_level: usize,
            config: ACSTAConfig,
            parents: Vec<ErrorGraphEdge>,
            self_loops: Vec<u32>,
            back_edges: Vec<ErrorGraphEdge>,
        ) -> Self {
            Self {
                error_level,
                config,
                parents,
                self_loops,
                back_edges,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{cell::RefCell, collections::VecDeque, rc::Rc};

    use taco_display_utils::join_iterator;
    use taco_interval_ta::builder::IntervalTABuilder;

    use taco_model_checker::internal_spec::upwards_closed_set::UpwardsClosedSet;
    use taco_smt_encoder::SMTSolverBuilder;
    use taco_threshold_automaton::{
        expressions::{
            BooleanExpression, ComparisonOp, IntegerExpression, Location, Parameter, Variable,
        },
        general_threshold_automaton::{
            Action,
            builder::{GeneralThresholdAutomatonBuilder, RuleBuilder},
        },
        lia_threshold_automaton::LIAThresholdAutomaton,
    };

    use crate::{
        acs_threshold_automaton::{
            ACSInterval, ACSLocation, ACSThresholdAutomaton, CSIntervalConstraint, CSRule,
            configuration::{ACSIntervalState, ACSLocState, ACSTAConfig},
        },
        error_graph::{NodeRef, edge::ErrorGraphEdge, node::ErrorGraphNode},
    };

    fn get_test_ta() -> ACSThresholdAutomaton {
        let ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_variables([Variable::new("x"), Variable::new("y")])
            .unwrap()
            .with_locations([
                Location::new("l1"),
                Location::new("l2"),
                Location::new("l3"),
            ])
            .unwrap()
            .with_parameter(Parameter::new("n"))
            .unwrap()
            .initialize()
            .with_resilience_condition(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Param(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(3)),
            ))
            .unwrap()
            .with_initial_location_constraints([
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("l2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("l3"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ])
            .unwrap()
            .with_initial_variable_constraints([
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("x"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("y"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ])
            .unwrap()
            .with_rule(
                RuleBuilder::new(0, Location::new("l1"), Location::new("l2"))
                    .with_action(
                        Action::new(
                            Variable::new("x"),
                            IntegerExpression::Const(1)
                                + IntegerExpression::Atom(Variable::new("x")),
                        )
                        .unwrap(),
                    )
                    .build(),
            )
            .unwrap()
            .build();
        let lia_ta = LIAThresholdAutomaton::try_from(ta).unwrap();
        let mut interval_tas = IntervalTABuilder::new(lia_ta, SMTSolverBuilder::default(), vec![])
            .build()
            .unwrap();
        let interval_ta = interval_tas.next().unwrap();
        assert!(interval_tas.next().is_none());
        ACSThresholdAutomaton::from(interval_ta)
    }

    #[test]
    fn test_getters() {
        let edge1 = ErrorGraphEdge::new(
            &CSRule::new_mock(
                0,
                ACSLocation::new_mock(1),
                ACSLocation::new_mock(2),
                CSIntervalConstraint::True,
                Vec::new(),
            ),
            Rc::new(RefCell::new(ErrorGraphNode {
                error_level: 0,
                config: ACSTAConfig::new_mock_from_vecs(Vec::new(), Vec::new()),
                parents: Vec::new(),
                self_loops: Vec::new(),
                back_edges: Vec::new(),
            })),
        );

        let edge2 = ErrorGraphEdge::new(
            &CSRule::new_mock(
                3,
                ACSLocation::new_mock(1),
                ACSLocation::new_mock(2),
                CSIntervalConstraint::True,
                Vec::new(),
            ),
            Rc::new(RefCell::new(ErrorGraphNode {
                error_level: 0,
                config: ACSTAConfig::new_mock_from_vecs(Vec::new(), Vec::new()),
                parents: Vec::new(),
                self_loops: Vec::new(),
                back_edges: Vec::new(),
            })),
        );

        let node = ErrorGraphNode {
            error_level: 42,
            config: ACSTAConfig::new_mock_from_vecs(Vec::new(), Vec::new()),
            parents: vec![edge1.clone()],
            self_loops: vec![1, 2, 3],
            back_edges: vec![edge2.clone()],
        };

        assert_eq!(node.error_level(), 42);
        assert_eq!(
            node.config(),
            &ACSTAConfig::new_mock_from_vecs(Vec::new(), Vec::new())
        );
        assert_eq!(
            node.self_loops().cloned().collect::<Vec<_>>(),
            vec![1, 2, 3]
        );
        assert_eq!(node.parents().collect::<Vec<_>>(), vec![&edge1]);
        assert_eq!(node.back_edges().collect::<Vec<_>>(), vec![&edge2]);
    }

    #[test]
    fn test_new_roots_from_spec_single() {
        let ta = get_test_ta();

        let loc_l3 = ta.to_cs_loc(&Location::new("l3"));

        let spec = UpwardsClosedSet::new_cover([Location::new("l3")]);

        let created_node_map = ErrorGraphNode::new_roots_from_spec(&spec, &ta);
        let created_nodes = created_node_map
            .get_all_values()
            .map(|n| n.borrow().clone())
            .collect::<Vec<_>>();

        let mut loc_state = ACSLocState::new_empty(&ta);
        loc_state[loc_l3] = 1;

        let expected_nodes = ACSIntervalState::all_possible_interval_configs(&ta)
            .into_iter()
            .map(|is| ErrorGraphNode {
                error_level: 0,
                config: ACSTAConfig::new_mock(loc_state.clone(), is),
                parents: Vec::new(),
                self_loops: Vec::new(),
                back_edges: Vec::new(),
            })
            .collect::<Vec<_>>();

        assert!(created_nodes.iter().all(|n| expected_nodes.contains(n)));
        assert!(expected_nodes.iter().all(|n| created_nodes.contains(n)));
    }

    #[test]
    fn test_new_roots_from_spec_all_cover() {
        let ta = get_test_ta();

        let loc_l1 = ta.to_cs_loc(&Location::new("l1"));
        let loc_l2 = ta.to_cs_loc(&Location::new("l2"));
        let loc_l3 = ta.to_cs_loc(&Location::new("l3"));

        let spec = UpwardsClosedSet::new_cover([
            Location::new("l3"),
            Location::new("l2"),
            Location::new("l1"),
        ]);

        let created_node_map = ErrorGraphNode::new_roots_from_spec(&spec, &ta);
        let created_nodes = created_node_map
            .get_all_values()
            .map(|n| n.borrow().clone())
            .collect::<Vec<_>>();

        let mut loc_state = ACSLocState::new_empty(&ta);
        loc_state[loc_l3] = 1;
        loc_state[loc_l2] = 1;
        loc_state[loc_l1] = 1;

        let expected_nodes = ACSIntervalState::all_possible_interval_configs(&ta)
            .into_iter()
            .map(|is| ErrorGraphNode {
                error_level: 0,
                config: ACSTAConfig::new_mock(loc_state.clone(), is),
                parents: Vec::new(),
                self_loops: Vec::new(),
                back_edges: Vec::new(),
            })
            .collect::<Vec<_>>();

        assert!(created_nodes.iter().all(|n| expected_nodes.contains(n)));
        assert!(expected_nodes.iter().all(|n| created_nodes.contains(n)));
    }

    #[test]
    fn test_new_roots_from_spec_multi_cover() {
        let ta = get_test_ta();

        let loc_l1 = ta.to_cs_loc(&Location::new("l1"));
        let loc_l2 = ta.to_cs_loc(&Location::new("l2"));
        let loc_l3 = ta.to_cs_loc(&Location::new("l3"));

        let spec = UpwardsClosedSet::new_cover([Location::new("l3")])
            | UpwardsClosedSet::new_cover([Location::new("l2")])
            | UpwardsClosedSet::new_cover([Location::new("l1")]);

        let created_node_map = ErrorGraphNode::new_roots_from_spec(&spec, &ta);
        let created_nodes = created_node_map
            .get_all_values()
            .map(|n| n.borrow().clone())
            .collect::<Vec<_>>();

        let mut loc_state_3 = ACSLocState::new_empty(&ta);
        loc_state_3[loc_l3] = 1;

        let mut loc_state_2 = ACSLocState::new_empty(&ta);
        loc_state_2[loc_l2] = 1;

        let mut loc_state_1 = ACSLocState::new_empty(&ta);
        loc_state_1[loc_l1] = 1;

        let expected_nodes = ACSIntervalState::all_possible_interval_configs(&ta)
            .into_iter()
            .flat_map(|is| {
                [
                    ErrorGraphNode {
                        error_level: 0,
                        config: ACSTAConfig::new_mock(loc_state_3.clone(), is.clone()),
                        parents: Vec::new(),
                        self_loops: Vec::new(),
                        back_edges: Vec::new(),
                    },
                    ErrorGraphNode {
                        error_level: 0,
                        config: ACSTAConfig::new_mock(loc_state_2.clone(), is.clone()),
                        parents: Vec::new(),
                        self_loops: Vec::new(),
                        back_edges: Vec::new(),
                    },
                    ErrorGraphNode {
                        error_level: 0,
                        config: ACSTAConfig::new_mock(loc_state_1.clone(), is),
                        parents: Vec::new(),
                        self_loops: Vec::new(),
                        back_edges: Vec::new(),
                    },
                ]
            })
            .collect::<Vec<_>>();

        assert!(created_nodes.iter().all(|n| expected_nodes.contains(n)));
        assert!(expected_nodes.iter().all(|n| created_nodes.contains(n)));
    }

    #[test]
    fn test_new_compute_predecessor_ta_rule_not_exec_inc_all_cover() {
        let ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_variables([Variable::new("x"), Variable::new("y")])
            .unwrap()
            .with_locations([
                Location::new("l1"),
                Location::new("l2"),
                Location::new("l3"),
            ])
            .unwrap()
            .with_parameter(Parameter::new("n"))
            .unwrap()
            .initialize()
            .with_resilience_condition(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Param(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(3)),
            ))
            .unwrap()
            .with_initial_location_constraints([
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("l2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("l3"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ])
            .unwrap()
            .with_initial_variable_constraints([
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("x"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("y"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ])
            .unwrap()
            .with_rule(
                RuleBuilder::new(0, Location::new("l1"), Location::new("l1"))
                    .with_guard(BooleanExpression::False) // disabled rule
                    .with_action(
                        Action::new(
                            Variable::new("x"),
                            IntegerExpression::Const(1)
                                + IntegerExpression::Atom(Variable::new("x")),
                        )
                        .unwrap(),
                    )
                    .build(),
            )
            .unwrap()
            .build();
        let lia_ta = LIAThresholdAutomaton::try_from(ta).unwrap();
        let mut interval_tas = IntervalTABuilder::new(lia_ta, SMTSolverBuilder::default(), vec![])
            .build()
            .unwrap();
        let interval_ta = interval_tas.next().unwrap();
        assert!(interval_tas.next().is_none());
        let ta = ACSThresholdAutomaton::from(interval_ta);

        let loc_l1 = ta.to_cs_loc(&Location::new("l1"));
        let loc_l2 = ta.to_cs_loc(&Location::new("l2"));
        let loc_l3 = ta.to_cs_loc(&Location::new("l3"));

        let var_x = ta.to_cs_var(&Variable::new("x"));

        let spec = UpwardsClosedSet::new_cover([
            Location::new("l3"),
            Location::new("l2"),
            Location::new("l1"),
        ]);

        // The target config will be (1, 1, 1) and should already be a
        // fix point
        let mut cfg_node_map = ErrorGraphNode::new_roots_from_spec(&spec, &ta);
        let mut to_explore_queue: VecDeque<NodeRef> = VecDeque::new();

        let mut loc_state = ACSLocState::new_empty(&ta);
        loc_state[loc_l3] = 1;
        loc_state[loc_l2] = 1;
        loc_state[loc_l1] = 1;

        let mut explored_is = ACSIntervalState::new_mock_zero(&ta);
        explored_is[var_x] = ACSInterval::new_mock(1);

        // Get the node out of the map or it won't be updated
        let node_to_explore = cfg_node_map
            .values()
            .find(|n| *n.borrow().config.interval_state() == explored_is)
            .unwrap()
            .clone();

        ErrorGraphNode::compute_predecessors_and_insert_to_graph(
            &mut cfg_node_map,
            &mut to_explore_queue,
            &node_to_explore,
            &ta,
        );

        assert_eq!(
            to_explore_queue.len(),
            0,
            "Got configs {:?}",
            join_iterator(
                to_explore_queue
                    .iter()
                    .map(|n| n.borrow().config.display(&ta)),
                ", "
            )
        );

        let created_nodes = cfg_node_map
            .get_all_values()
            .map(|n| n.borrow().clone())
            .collect::<Vec<_>>();

        let expected_nodes = ACSIntervalState::all_possible_interval_configs(&ta)
            .into_iter()
            .map(|is| ErrorGraphNode {
                error_level: 0,
                config: ACSTAConfig::new_mock(loc_state.clone(), is),
                parents: Vec::new(),
                self_loops: vec![],
                back_edges: Vec::new(),
            })
            .collect::<Vec<_>>();

        assert!(created_nodes.iter().all(|n| expected_nodes.contains(n)));
        assert!(expected_nodes.iter().all(|n| created_nodes.contains(n)));
    }

    #[test]
    fn test_new_compute_predecessor_ta_only_loc_update_all_cover() {
        let ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_variables([Variable::new("x"), Variable::new("y")])
            .unwrap()
            .with_locations([
                Location::new("l1"),
                Location::new("l2"),
                Location::new("l3"),
            ])
            .unwrap()
            .with_parameter(Parameter::new("n"))
            .unwrap()
            .initialize()
            .with_resilience_condition(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Param(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(3)),
            ))
            .unwrap()
            .with_initial_location_constraints([
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("l2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("l3"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ])
            .unwrap()
            .with_initial_variable_constraints([
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("x"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("y"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ])
            .unwrap()
            .with_rule(RuleBuilder::new(0, Location::new("l1"), Location::new("l2")).build())
            .unwrap()
            .build();
        let lia_ta = LIAThresholdAutomaton::try_from(ta).unwrap();
        let mut interval_tas = IntervalTABuilder::new(lia_ta, SMTSolverBuilder::default(), vec![])
            .build()
            .unwrap();
        let interval_ta = interval_tas.next().unwrap();
        assert!(interval_tas.next().is_none());
        let ta = ACSThresholdAutomaton::from(interval_ta);

        let loc_l1 = ta.to_cs_loc(&Location::new("l1"));
        let loc_l2 = ta.to_cs_loc(&Location::new("l2"));
        let loc_l3 = ta.to_cs_loc(&Location::new("l3"));

        let var_x = ta.to_cs_var(&Variable::new("x"));

        let spec = UpwardsClosedSet::new_cover([
            Location::new("l3"),
            Location::new("l2"),
            Location::new("l1"),
        ]);

        // The target config will be (1, 1, 1) and should already be a
        // fix point
        let mut cfg_node_map = ErrorGraphNode::new_roots_from_spec(&spec, &ta);
        let mut to_explore_queue: VecDeque<NodeRef> = VecDeque::new();

        let mut loc_state = ACSLocState::new_empty(&ta);
        loc_state[loc_l3] = 1;
        loc_state[loc_l2] = 1;
        loc_state[loc_l1] = 1;

        let mut is_to_explore = ACSIntervalState::new_mock_zero(&ta);
        is_to_explore[var_x] = ACSInterval::new_mock(1);

        // Get the node out of the map or it won't be updated
        let node_to_explore = cfg_node_map
            .values()
            .find(|n| *n.borrow().config.interval_state() == is_to_explore.clone())
            .unwrap()
            .clone();

        ErrorGraphNode::compute_predecessors_and_insert_to_graph(
            &mut cfg_node_map,
            &mut to_explore_queue,
            &node_to_explore,
            &ta,
        );

        assert_eq!(
            to_explore_queue.len(),
            1,
            "Got configs {}",
            join_iterator(
                to_explore_queue
                    .iter()
                    .map(|n| n.borrow().config.display(&ta)),
                ", "
            )
        );

        let mut new_loc_state = ACSLocState::new_empty(&ta);
        new_loc_state[loc_l3] = 1;
        new_loc_state[loc_l2] = 0;
        new_loc_state[loc_l1] = 2;

        let expected_node_to_explore = ErrorGraphNode {
            error_level: 1,
            config: ACSTAConfig::new_mock(new_loc_state, is_to_explore.clone()),
            parents: vec![ErrorGraphEdge::new_mock_with_id(0, node_to_explore.clone())],
            self_loops: Vec::new(),
            back_edges: Vec::new(),
        };

        assert_eq!(
            to_explore_queue,
            VecDeque::from([expected_node_to_explore.clone().into()])
        );

        let created_nodes = cfg_node_map
            .get_all_values()
            .map(|n| n.borrow().clone())
            .collect::<Vec<_>>();

        let expected_nodes = ACSIntervalState::all_possible_interval_configs(&ta)
            .into_iter()
            .map(|is| ErrorGraphNode {
                error_level: 0,
                config: ACSTAConfig::new_mock(loc_state.clone(), is),
                parents: Vec::new(),
                self_loops: vec![],
                back_edges: Vec::new(),
            })
            .chain([expected_node_to_explore])
            .collect::<Vec<_>>();

        assert!(created_nodes.iter().all(|n| expected_nodes.contains(n)));
        assert!(expected_nodes.iter().all(|n| created_nodes.contains(n)));
    }

    #[test]
    fn test_new_compute_predecessor_ta_only_self_loop_with_inc_all_cover() {
        let ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_variables([Variable::new("x"), Variable::new("y")])
            .unwrap()
            .with_locations([
                Location::new("l1"),
                Location::new("l2"),
                Location::new("l3"),
            ])
            .unwrap()
            .with_parameter(Parameter::new("n"))
            .unwrap()
            .initialize()
            .with_resilience_condition(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Param(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(3)),
            ))
            .unwrap()
            .with_initial_location_constraints([
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("l2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("l3"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ])
            .unwrap()
            .with_initial_variable_constraints([
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("x"))),
                    ComparisonOp::Lt,
                    Box::new(IntegerExpression::Const(1)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("y"))),
                    ComparisonOp::Lt,
                    Box::new(IntegerExpression::Const(1)),
                ),
            ])
            .unwrap()
            .with_rule(
                RuleBuilder::new(0, Location::new("l1"), Location::new("l1"))
                    .with_action(
                        Action::new(
                            Variable::new("x"),
                            IntegerExpression::Const(1)
                                + IntegerExpression::Atom(Variable::new("x")),
                        )
                        .unwrap(),
                    )
                    .build(),
            )
            .unwrap()
            .build();
        let lia_ta = LIAThresholdAutomaton::try_from(ta).unwrap();
        let mut interval_tas = IntervalTABuilder::new(lia_ta, SMTSolverBuilder::default(), vec![])
            .build()
            .unwrap();
        let interval_ta = interval_tas.next().unwrap();
        assert!(interval_tas.next().is_none());
        let ta = ACSThresholdAutomaton::from(interval_ta);

        let loc_l1 = ta.to_cs_loc(&Location::new("l1"));
        let loc_l2 = ta.to_cs_loc(&Location::new("l2"));
        let loc_l3 = ta.to_cs_loc(&Location::new("l3"));

        let var_x = ta.to_cs_var(&Variable::new("x"));

        let spec = UpwardsClosedSet::new_cover([
            Location::new("l3"),
            Location::new("l2"),
            Location::new("l1"),
        ]);

        // The target config will be (1, 1, 1) and should already be a
        // fix point
        let mut cfg_node_map = ErrorGraphNode::new_roots_from_spec(&spec, &ta);
        let mut to_explore_queue: VecDeque<NodeRef> = VecDeque::new();

        let mut loc_state = ACSLocState::new_empty(&ta);
        loc_state[loc_l3] = 1;
        loc_state[loc_l2] = 1;
        loc_state[loc_l1] = 1;

        let mut explored_is = ACSIntervalState::new_mock_zero(&ta);
        explored_is[var_x] = ACSInterval::new_mock(1);

        // Get the node out of the map or it won't be updated
        let node_to_explore = cfg_node_map
            .values()
            .find(|n| *n.borrow().config.interval_state() == explored_is)
            .unwrap()
            .clone();

        ErrorGraphNode::compute_predecessors_and_insert_to_graph(
            &mut cfg_node_map,
            &mut to_explore_queue,
            &node_to_explore,
            &ta,
        );

        assert_eq!(
            to_explore_queue.len(),
            0,
            "Got configs {:?}",
            join_iterator(
                to_explore_queue
                    .iter()
                    .map(|n| n.borrow().config.display(&ta)),
                ", "
            )
        );

        let created_nodes = cfg_node_map
            .get_all_values()
            .map(|n| n.borrow().clone())
            .collect::<Vec<_>>();

        // all nodes are already error states, so we expect them to stay
        let expected_nodes = ACSIntervalState::all_possible_interval_configs(&ta)
            .into_iter()
            .map(|is| {
                // in the abstraction using rule x = [1,\infty[, y = [0,1[ we could
                // have stayed in the same interval
                // -> insert a self-loop
                if is == explored_is {
                    return ErrorGraphNode {
                        error_level: 0,
                        config: ACSTAConfig::new_mock(loc_state.clone(), is),
                        parents: Vec::new(),
                        self_loops: vec![0],
                        back_edges: Vec::new(),
                    };
                }

                if is == ACSIntervalState::new_mock_zero(&ta) {
                    return ErrorGraphNode {
                        error_level: 0,
                        config: ACSTAConfig::new_mock(
                            loc_state.clone(),
                            ACSIntervalState::new_mock_zero(&ta),
                        ),
                        parents: vec![ErrorGraphEdge::new_mock_with_id(
                            0,
                            ErrorGraphNode {
                                error_level: 0,
                                config: ACSTAConfig::new_mock(
                                    loc_state.clone(),
                                    explored_is.clone(),
                                ),
                                parents: Vec::new(),
                                self_loops: vec![0],
                                back_edges: Vec::new(),
                            }
                            .into(),
                        )],
                        self_loops: vec![],
                        back_edges: Vec::new(),
                    };
                }

                // Don't update

                ErrorGraphNode {
                    error_level: 0,
                    config: ACSTAConfig::new_mock(loc_state.clone(), is),
                    parents: Vec::new(),
                    self_loops: vec![],
                    back_edges: Vec::new(),
                }
            })
            .collect::<Vec<_>>();

        assert!(
            created_nodes.iter().all(|n| expected_nodes.contains(n)),
            "got: {}\n expected: {}\n additional: {}",
            join_iterator(
                created_nodes
                    .iter()
                    .map(|n| { n.config.display_compact(&ta) }),
                ","
            ),
            join_iterator(
                expected_nodes
                    .iter()
                    .map(|n| { n.config.display_compact(&ta) }),
                ","
            ),
            join_iterator(
                created_nodes
                    .iter()
                    .filter(|n| !expected_nodes.contains(n))
                    .map(|n| { n.config.display_compact(&ta) }),
                "; "
            )
        );
        assert!(expected_nodes.iter().all(|n| created_nodes.contains(n)));
    }
}
