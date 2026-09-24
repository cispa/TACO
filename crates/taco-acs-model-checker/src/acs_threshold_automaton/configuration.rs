//! Configurations of a [`ACSThresholdAutomaton`]
//!
//! This module contains the type definitions for configurations of a
//! [ `ACSThresholdAutomaton`]. These types are designed to have a small memory
//! footprint and should be easily computable.
//! This also means that when working with configurations, there is no extensive
//! validation that is performed. In particular, one must ensure that
//! configurations, locations, and intervals etc. from different threshold
//! automata are not mixed. Otherwise panics can arise, and the results will not
//! have any meaning.

use std::{
    collections::HashSet,
    ops::{Index, IndexMut},
    vec,
};

use taco_display_utils::display_iterator_stable_order;
use taco_interval_ta::{IntervalActionEffect, IntervalConstraint};

use taco_model_checker::internal_spec::upwards_closed_set::{
    UpwardsClosedClause, UpwardsClosedSet,
};
use taco_smt_encoder::{
    SMTExpr, SMTSolver,
    expression_encoding::{EncodeToSMT, SMTVariableContext},
};
use taco_threshold_automaton::expressions::{Location, Parameter, Variable};

use crate::{
    acs_threshold_automaton::{
        ACSInterval, ACSLocation, ACSThresholdAutomaton, CSIntervalAction, CSRule, CSVariable,
    },
    partial_ord::{PartialOrdCompResult, PartialOrder},
};

pub(crate) mod partially_ordered_cfg_map;

/// Configuration of a [`ACSThresholdAutomaton`]
///
/// This struct represents a configuration, i.e. an assignment of intervals for
/// all shared variables and a number of processes in each location.
///
/// Use these configurations with care. Configurations of different automata
/// should never be indexed by locations, variables or intervals of other
/// automata.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ACSTAConfig {
    /// Location state specifying how many processes are in each location
    loc_state: ACSLocState,
    /// Interval state specifying the current interval for each variable
    interval_state: ACSIntervalState,
}

impl ACSTAConfig {
    /// Get the interval state of the configuration
    pub fn interval_state(&self) -> &ACSIntervalState {
        &self.interval_state
    }

    /// Get the location state of the configuration
    pub fn location_state(&self) -> &ACSLocState {
        &self.loc_state
    }

    /// Check whether the current configuration is an initial configuration of
    /// the threshold automaton
    pub fn is_initial(&self, ta: &ACSThresholdAutomaton) -> bool {
        let locs_all_init = self
            .loc_state
            .into_iterator_loc_n_procs()
            .filter(|(_, n_procs)| *n_procs > 0)
            .all(|(loc, _)| ta.is_initial_loc(&loc));

        let intervals_all_init = self
            .interval_state
            .into_iterator_variable_interval()
            .all(|(var, interval)| ta.is_initial_interval(&var, &interval));

        locs_all_init && intervals_all_init
    }

    /// Compute all predecessors of the configuration that could stem from
    /// rule `r` being applied
    ///
    /// Note that the iterator returned here might contain comparable elements.
    /// Computing the *minimal* basis must be handled when collecting this
    /// iterator
    /// This function returns `None` if the rule contains a reset, and the
    /// variable the reset has been applied to is not in its 0 interval.
    pub fn compute_potential_predecessors(
        &self,
        rule: &CSRule,
        ta: &ACSThresholdAutomaton,
    ) -> Option<impl Iterator<Item = Self>> {
        let res_acts = rule
            .actions()
            .filter(|a| a.effect() == &IntervalActionEffect::Reset)
            .collect::<Vec<_>>();
        if !res_acts.is_empty() {
            for res_act in res_acts.into_iter() {
                let reset_var = res_act.variable();
                if self.interval_state[reset_var] != ta.get_zero_interval(reset_var) {
                    return None;
                }
            }
        }

        let location_state = self.loc_state.compute_predecessors_min_basis(rule);

        Some(
            self.interval_state
                .compute_all_predecessor_configs(rule, ta)
                .into_iter()
                .filter(|is| rule.guard().is_satisfied(is))
                .map(move |interval_cfg| Self {
                    loc_state: location_state.clone(),
                    interval_state: interval_cfg,
                }),
        )
    }

    /// Compute all configurations that correspond to an error state in the
    /// given disjunction over target configurations
    pub fn from_disjunct_target(
        spec: &UpwardsClosedSet,
        ta: &ACSThresholdAutomaton,
    ) -> impl Iterator<Item = ACSTAConfig> {
        spec.upwards_closed_clauses()
            .flat_map(|target| Self::from_target_config(target, ta))
    }

    /// Compute a goal configuration from a single [`TargetConfig`]
    pub fn from_target_config(
        spec: &UpwardsClosedClause,
        ta: &ACSThresholdAutomaton,
    ) -> HashSet<Self> {
        let interval_constr = ta
            .interval_ta
            .get_interval_constraint(spec.variable_constr())
            .expect("Failed to derive interval constraint for target");

        let interval_cfgs = ACSIntervalState::get_target_interval_configs(interval_constr, ta);

        let location_cfg = ACSLocState::compute_target_cfg(spec, ta);

        interval_cfgs
            .into_iter()
            .map(|interval_cfg| Self {
                loc_state: location_cfg.clone(),
                interval_state: interval_cfg,
            })
            .collect()
    }

    /// Get a string representation of the configuration
    pub fn display(&self, ta: &ACSThresholdAutomaton) -> String {
        format!(
            "locations: ({}), variables: ({})",
            self.loc_state.display(ta),
            self.interval_state.display(ta)
        )
    }

    /// Get a compact string representation of the configuration without
    /// locations that are not covered by processes or variables that are zero
    pub fn display_compact(&self, ta: &ACSThresholdAutomaton) -> String {
        format!(
            "locations: ({}), variables: ({})",
            self.loc_state.display_compact(ta),
            self.interval_state.display_compact(ta)
        )
    }

    /// Encode the conditions this abstract configuration places on the
    /// corresponding concrete configurations into an SMT expression
    pub fn encode_config_constraints_to_smt<
        C: SMTVariableContext<Parameter> + SMTVariableContext<Variable> + SMTVariableContext<Location>,
    >(
        &self,
        ta: &ACSThresholdAutomaton,
        solver: &SMTSolver,
        ctx: &C,
    ) -> SMTExpr {
        // encode at least required number of procs
        let loc_constr = self
            .location_state()
            .into_iterator_loc_n_procs()
            .filter(|(_, n)| *n > 0)
            .map(|(loc, n)| {
                let loc = ctx
                    .get_expr_for(ta.idx_ctx.get_loc(&loc))
                    .expect("Expected location SMT variable to be declared");

                solver.gte(loc, solver.numeral(n))
            });

        let interval_constr = self
            .interval_state()
            .into_iterator_variable_interval()
            .filter(|(v, _)| {
                // We do not encode intervals of the replacement variables as
                // these variables do not appear in the original automaton but
                // we use the original automaton in the encoding.
                // Correctness of the interval abstraction is guaranteed because
                // the single variable behaves the same as the sum of two
                // variables and the correctness of steps is ensured by encoding
                // the rule guards
                // TODO: remove once ordering support is ready
                !ta.interval_ta
                    .get_helper_vars_for_sumvars()
                    .contains_key(ta.idx_ctx.get_var(v))
            })
            .map(|(var, i)| {
                let i = ta.idx_ctx.get_interval(&var, &i);
                let var = ta.idx_ctx.get_var(&var);

                let interval_expr = i.encode_into_boolean_expr(var);

                interval_expr
                    .encode_to_smt_with_ctx(solver, ctx)
                    .expect("Failed to encode interval constraint")
            });

        solver.and_many(loc_constr.chain(interval_constr))
    }
}

impl PartialOrder for ACSTAConfig {
    #[inline(always)]
    fn part_cmp(&self, other: &Self) -> PartialOrdCompResult {
        let interval_comp = self.interval_state.part_cmp(&other.interval_state);
        if interval_comp == PartialOrdCompResult::Incomparable {
            return PartialOrdCompResult::Incomparable;
        }

        let loc_comp = self.loc_state.part_cmp(&other.loc_state);
        interval_comp.combine(loc_comp)
    }
}

/// Assignment of variables to their current value
///
/// An interval state represents a valuation of the shared variables of a
/// threshold automaton with interval abstraction.
///
/// Use this type with care. `IntervalState`s of different automata
/// should never be indexed by variables or intervals of other automata.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ACSIntervalState {
    /// Intervals of the configuration
    /// Index of the entry represents the variable
    v_to_interval: Vec<ACSInterval>,
}

impl ACSIntervalState {
    pub fn into_iterator_variable_interval(
        &self,
    ) -> impl Iterator<Item = (CSVariable, ACSInterval)> {
        self.v_to_interval
            .iter()
            .enumerate()
            .map(|(var, interval)| (CSVariable(var), *interval))
    }

    /// Create a new interval configuration where all variables are in the
    /// interval mapped to zero
    ///
    /// The resulting configuration of this function should not be used directly
    /// as it does not necessarily correspond to a valid configuration. It
    /// should only be used for initialization purposes.
    fn new_cfg_all_zero_interval(ta: &ACSThresholdAutomaton) -> Self {
        Self {
            v_to_interval: vec![ACSInterval(0); ta.variables().count()],
        }
    }

    /// Compute all interval states that are possible in the threshold automaton
    pub fn all_possible_interval_configs(ta: &ACSThresholdAutomaton) -> Vec<ACSIntervalState> {
        let zero_interval = Vec::from([Self::new_cfg_all_zero_interval(ta)]);

        ta.variables().fold(zero_interval, |cfgs, var| {
            cfgs.iter()
                .flat_map(|cfg| {
                    ta.get_all_intervals(var).map(|interval| {
                        let mut new_cfg = cfg.clone();
                        new_cfg[var] = *interval;
                        new_cfg
                    })
                })
                .collect()
        })
    }

    /// Compute all interval states that are allowed by the given interval
    /// constraint in the threshold automaton
    pub fn get_target_interval_configs(
        constr: IntervalConstraint,
        ta: &ACSThresholdAutomaton,
    ) -> Vec<ACSIntervalState> {
        if constr == IntervalConstraint::True {
            return Self::all_possible_interval_configs(ta);
        }

        let zero_interval = Vec::from([Self::new_cfg_all_zero_interval(ta)]);

        ta.variables().fold(zero_interval, |cfgs, var| {
            cfgs.iter()
                .flat_map(|cfg| {
                    let org_var = ta.idx_ctx.get_var(var);

                    ta.get_interval_ta()
                        .get_enabled_intervals(&constr, org_var)
                        .map(|interval| {
                            let interval = ta.idx_ctx.to_cs_interval(var, interval);
                            let mut new_cfg = cfg.clone();
                            new_cfg[var] = interval;
                            new_cfg
                        })
                })
                .collect()
        })
    }

    /// Compute all potential predecessor interval configurations of one rule application
    pub fn compute_all_predecessor_configs(
        &self,
        rule: &CSRule,
        ta: &ACSThresholdAutomaton,
    ) -> Vec<Self> {
        // for each action add the predecessor where the action had an affect on
        // the interval, but also the interval state, where the interval was unaffected
        rule.actions()
            .fold(Vec::from([self.clone()]), |predecessors, act| {
                // for each computed predecessor compute intervals before action
                predecessors
                    .into_iter()
                    .flat_map(|interval_cfg| {
                        Self::compute_possible_interval_state_before_application_of_act(
                            &interval_cfg,
                            act,
                            ta,
                        )
                    })
                    .collect()
            })
            .into_iter()
            .filter(|is| rule.is_guard_enabled(is))
            .collect()
    }

    /// Compute all possible interval configurations before the application of
    /// the action
    ///
    /// Concretely, for
    /// - Increment actions: The increment could have lead to jumping to the
    ///   next interval, or could have stayed in the current interval.
    /// - Decrement actions: The decrement could have lead to a jump to a
    ///   smaller interval or could have stayed in the current interval.
    /// - Reset actions: A reset will always go to the 0 interval.
    fn compute_possible_interval_state_before_application_of_act(
        &self,
        act: &CSIntervalAction,
        ta: &ACSThresholdAutomaton,
    ) -> HashSet<Self> {
        let mut possible_pred_intervals = HashSet::new();

        match act.effect() {
            IntervalActionEffect::Inc(i) => {
                let prev_interval = ta.get_prev_interval(act.variable(), &self[act.variable()]);

                // check whether we could have stayed in the interval
                // if yes, add back the current interval state
                if !ta
                    .idx_ctx
                    .get_interval(act.variable(), &self[act.variable()])
                    .check_sub_always_out_of_interval(*i)
                {
                    possible_pred_intervals.insert(self.clone());
                }

                // check if a smaller interval exists, if yes insert the interval
                // state with `act.variable()` is in that interval
                if let Some(prev_interval) = prev_interval {
                    let mut prev_interval_cfg = self.clone();
                    prev_interval_cfg[act.variable()] = prev_interval;

                    possible_pred_intervals.insert(prev_interval_cfg);
                }
            }
            IntervalActionEffect::Dec(d) => {
                let next_interval = ta.get_next_interval(act.variable(), &self[act.variable()]);

                // check whether we could have stayed in the interval
                // if yes, add back the current interval state
                if !ta
                    .idx_ctx
                    .get_interval(act.variable(), &self[act.variable()])
                    .check_add_always_out_of_interval(*d)
                {
                    possible_pred_intervals.insert(self.clone());
                }

                // check if a bigger interval exists, if yes insert the interval
                // state with `act.variable()` is in that interval
                if let Some(nxt_interval) = next_interval {
                    let mut nxt_interval_cfg = self.clone();
                    nxt_interval_cfg[act.variable()] = nxt_interval;

                    possible_pred_intervals.insert(nxt_interval_cfg);
                }
            }
            IntervalActionEffect::Reset => {
                // the previous
                let potential_intervals = ta.get_all_intervals(act.variable()).map(|interval| {
                    let mut new_cfg = self.clone();
                    new_cfg[act.variable()] = *interval;

                    new_cfg
                });

                possible_pred_intervals.extend(potential_intervals);
            }
        }

        possible_pred_intervals
    }

    /// Get a string representation of the interval state
    pub fn display(&self, ta: &ACSThresholdAutomaton) -> String {
        display_iterator_stable_order(
            self.into_iterator_variable_interval()
                .map(|(var, interval)| {
                    format!("{} : {}", var.display(ta), interval.display(&var, ta))
                }),
        )
    }

    /// Get a string representation of the interval state, leaving out variables
    /// in their zero interval
    pub fn display_compact(&self, ta: &ACSThresholdAutomaton) -> String {
        display_iterator_stable_order(
            self.into_iterator_variable_interval()
                .filter(|(var, interval)| ta.get_zero_interval(var) != *interval)
                .map(|(var, interval)| {
                    format!("{} : {}", var.display(ta), interval.display(&var, ta))
                }),
        )
    }
}

impl Index<&CSVariable> for ACSIntervalState {
    type Output = ACSInterval;

    fn index(&self, var: &CSVariable) -> &Self::Output {
        &self.v_to_interval[var.0]
    }
}

impl IndexMut<&CSVariable> for ACSIntervalState {
    fn index_mut(&mut self, var: &CSVariable) -> &mut Self::Output {
        &mut self.v_to_interval[var.0]
    }
}

impl Index<CSVariable> for ACSIntervalState {
    type Output = ACSInterval;

    fn index(&self, var: CSVariable) -> &Self::Output {
        &self.v_to_interval[var.0]
    }
}

impl IndexMut<CSVariable> for ACSIntervalState {
    fn index_mut(&mut self, var: CSVariable) -> &mut Self::Output {
        &mut self.v_to_interval[var.0]
    }
}

impl PartialOrder for ACSInterval {
    #[inline(always)]
    fn part_cmp(&self, other: &Self) -> PartialOrdCompResult {
        if self == other {
            return PartialOrdCompResult::Equal;
        }
        PartialOrdCompResult::Incomparable
    }
}

impl PartialOrder for ACSIntervalState {
    fn part_cmp(&self, other: &Self) -> PartialOrdCompResult {
        self.v_to_interval.part_cmp(&other.v_to_interval)
    }
}

/// Assignment of process counts to a location
///
/// The LocationState tracks how many processes are in each location of the
/// threshold automaton.
///
/// Use this type with care. `LocationState`s of different automata
/// should never be indexed by locations of other automata.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ACSLocState {
    /// Vector counting how many processes are in each location
    loc_state: Vec<u32>,
}

impl ACSLocState {
    /// Iterate over the configurations and the number of processes in these locations
    pub fn into_iterator_loc_n_procs(&self) -> impl Iterator<Item = (ACSLocation, u32)> {
        self.loc_state
            .iter()
            .enumerate()
            .map(|(i, n)| (ACSLocation(i), *n))
    }

    /// Compute the minimal basis of the predecessor
    ///
    /// This function assumes that `self` is the minimal basis of an upwards
    /// closed set of locations and computes the minimal basis of a state from
    /// which an element in `self` can be reached using `CSRule`.
    ///
    /// In particular this means that the predecessor generated here, can have
    /// more processes than `self`.
    pub fn compute_predecessors_min_basis(&self, rule: &CSRule) -> Self {
        let mut new_loc_state = self.clone();

        if self[rule.target()] > 0 {
            new_loc_state[rule.target()] -= 1;
        }

        new_loc_state[rule.source()] += 1;

        new_loc_state
    }

    fn new_all_zero(ta: &ACSThresholdAutomaton) -> Self {
        Self {
            loc_state: vec![0; ta.locations().count()],
        }
    }

    /// Get the [`ACSLocState`] that corresponds to the target configuration
    pub fn compute_target_cfg(spec: &UpwardsClosedClause, ta: &ACSThresholdAutomaton) -> Self {
        debug_assert!(
            spec.locs_to_uncover().count() == 0,
            "This model checker currently does not support reachability constraints, this should have been caught"
        );

        let mut target = Self::new_all_zero(ta);

        for (loc, n) in spec.locs_to_cover() {
            target[ta.idx_ctx.to_cs_loc(loc)] = *n;
        }

        target
    }

    /// Get a string representation of the location state
    pub fn display(&self, ta: &ACSThresholdAutomaton) -> String {
        display_iterator_stable_order(
            self.into_iterator_loc_n_procs()
                .map(|(l, n)| format!("{} : {}", l.display(ta), n)),
        )
    }

    /// Get a string representation of the location state, leaving out locations
    /// with zero processes in them
    pub fn display_compact(&self, ta: &ACSThresholdAutomaton) -> String {
        display_iterator_stable_order(
            self.into_iterator_loc_n_procs()
                .filter(|(_, n)| *n > 0)
                .map(|(l, n)| format!("{} : {}", l.display(ta), n)),
        )
    }
}

impl Index<&ACSLocation> for ACSLocState {
    type Output = u32;

    fn index(&self, loc: &ACSLocation) -> &Self::Output {
        &self.loc_state[loc.0]
    }
}

impl IndexMut<&ACSLocation> for ACSLocState {
    fn index_mut(&mut self, loc: &ACSLocation) -> &mut Self::Output {
        &mut self.loc_state[loc.0]
    }
}

impl Index<ACSLocation> for ACSLocState {
    type Output = u32;

    fn index(&self, loc: ACSLocation) -> &Self::Output {
        &self.loc_state[loc.0]
    }
}

impl IndexMut<ACSLocation> for ACSLocState {
    fn index_mut(&mut self, loc: ACSLocation) -> &mut Self::Output {
        &mut self.loc_state[loc.0]
    }
}

impl PartialOrder for ACSLocState {
    fn part_cmp(&self, other: &Self) -> PartialOrdCompResult {
        self.loc_state.part_cmp(&other.loc_state)
    }
}

#[cfg(test)]
mod mock_objects {
    use crate::acs_threshold_automaton::{
        ACSInterval, ACSThresholdAutomaton,
        configuration::{ACSIntervalState, ACSLocState, ACSTAConfig},
    };

    impl ACSTAConfig {
        pub fn new_mock_from_vecs(loc: Vec<u32>, intervals: Vec<ACSInterval>) -> Self {
            ACSTAConfig {
                loc_state: super::ACSLocState { loc_state: loc },
                interval_state: super::ACSIntervalState {
                    v_to_interval: intervals,
                },
            }
        }

        pub fn new_mock(loc: ACSLocState, int: ACSIntervalState) -> Self {
            Self {
                loc_state: loc,
                interval_state: int,
            }
        }
    }

    impl ACSLocState {
        pub fn new_empty(ta: &ACSThresholdAutomaton) -> Self {
            Self::new_all_zero(ta)
        }
    }

    impl ACSIntervalState {
        pub fn new_mock_from_vec(intervals: Vec<ACSInterval>) -> Self {
            ACSIntervalState {
                v_to_interval: intervals,
            }
        }

        pub fn new_mock_zero(ta: &ACSThresholdAutomaton) -> Self {
            Self::new_cfg_all_zero_interval(ta)
        }

        pub fn get_all_possible_intervals(ta: &ACSThresholdAutomaton) -> Vec<ACSIntervalState> {
            Self::all_possible_interval_configs(ta)
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{HashMap, HashSet};

    use taco_display_utils::join_iterator;
    use taco_interval_ta::{
        IntervalActionEffect, IntervalConstraint, builder::IntervalTABuilder, interval::Interval,
    };
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
            ACSInterval, ACSLocation, ACSThresholdAutomaton, CSIntervalAction,
            CSIntervalConstraint, CSRule, CSVariable,
            configuration::{ACSIntervalState, ACSLocState, ACSTAConfig},
        },
        partial_ord::{PartialOrdCompResult, PartialOrder},
    };

    #[test]
    fn test_cstaconfig_getters() {
        let config = ACSTAConfig {
            loc_state: ACSLocState {
                loc_state: vec![1, 2, 3],
            },
            interval_state: ACSIntervalState {
                v_to_interval: vec![ACSInterval(3), ACSInterval(2), ACSInterval(1)],
            },
        };
        assert_eq!(
            config.location_state(),
            &ACSLocState {
                loc_state: vec![1, 2, 3],
            }
        );
        assert_eq!(
            config.interval_state(),
            &ACSIntervalState {
                v_to_interval: vec![ACSInterval(3), ACSInterval(2), ACSInterval(1)],
            }
        );
    }

    #[test]
    fn test_cstaconfig_is_initial() {
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
                    .with_guard(BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("x"))),
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(2)),
                    ))
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
        // l2 == 0, l3 == 0, x == 0, y == 0
        let ta = ACSThresholdAutomaton::new(interval_ta);
        let l1 = ta.idx_ctx.to_cs_loc(&Location::new("l1"));
        let l2 = ta.idx_ctx.to_cs_loc(&Location::new("l2"));

        let mut loc_state = ACSLocState::new_all_zero(&ta);
        loc_state[l1] = 1;

        let config1 = ACSTAConfig {
            loc_state,
            interval_state: ACSIntervalState {
                v_to_interval: vec![ACSInterval(0), ACSInterval(0)],
            },
        };

        assert!(config1.is_initial(&ta));

        let mut loc_state = ACSLocState::new_all_zero(&ta);
        loc_state[l1] = 420;

        let config2 = ACSTAConfig {
            loc_state,
            interval_state: ACSIntervalState {
                v_to_interval: vec![ACSInterval(0), ACSInterval(0)],
            },
        };

        assert!(config2.is_initial(&ta));

        let mut loc_state = ACSLocState::new_all_zero(&ta);
        loc_state[l1] = 1;
        loc_state[l2] = 2;

        let config2 = ACSTAConfig {
            loc_state,
            interval_state: ACSIntervalState {
                v_to_interval: vec![ACSInterval(0), ACSInterval(0)],
            },
        };

        assert!(!config2.is_initial(&ta));

        let mut loc_state = ACSLocState::new_all_zero(&ta);
        loc_state[l1] = 1;

        let config2 = ACSTAConfig {
            loc_state,
            interval_state: ACSIntervalState {
                v_to_interval: vec![ACSInterval(0), ACSInterval(1)],
            },
        };

        assert!(!config2.is_initial(&ta));

        let mut loc_state = ACSLocState::new_all_zero(&ta);
        loc_state[l1] = 1;
        loc_state[l2] = 2;

        let config2 = ACSTAConfig {
            loc_state,
            interval_state: ACSIntervalState {
                v_to_interval: vec![ACSInterval(1), ACSInterval(1)],
            },
        };

        assert!(!config2.is_initial(&ta));
    }

    #[test]
    fn test_cstaconfig_compute_min_predecessor() {
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
                        ComparisonOp::Geq,
                        Box::new(IntegerExpression::Const(3)),
                    ))
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
        let cs_ta = ACSThresholdAutomaton::new(interval_ta);
        let var_x = cs_ta.idx_ctx.to_cs_var(&Variable::new("x"));
        let var_y = cs_ta.idx_ctx.to_cs_var(&Variable::new("y"));

        let mut interval_state = ACSIntervalState::new_cfg_all_zero_interval(&cs_ta);
        interval_state[var_x] = ACSInterval(1);
        interval_state[var_y] = ACSInterval(0);

        let rule = CSRule {
            id: 0,
            source: ACSLocation(0),
            target: ACSLocation(1),
            guard: CSIntervalConstraint::True,
            actions: vec![CSIntervalAction {
                var: var_x,
                effect: IntervalActionEffect::Inc(1),
            }],
        };

        let config = ACSTAConfig {
            loc_state: ACSLocState {
                loc_state: vec![0, 1, 0],
            },
            interval_state: interval_state.clone(),
        };

        let mut pred_1 = config.clone();
        pred_1.loc_state.loc_state = vec![1, 0, 0];

        let mut pred_2 = config.clone();
        pred_2.loc_state.loc_state = vec![1, 0, 0];
        pred_2.interval_state[var_x] = ACSInterval(0);

        let got_min_basis = config
            .compute_potential_predecessors(&rule, &cs_ta)
            .unwrap()
            .collect::<HashSet<_>>();
        let expected_min_basis = HashSet::from([pred_1, pred_2]);

        assert_eq!(got_min_basis, expected_min_basis);
    }

    #[test]
    fn test_compute_pred_none_if_var_of_reset_not_in_zero() {
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
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(2)),
                    ))
                    .with_action(
                        Action::new(Variable::new("x"), IntegerExpression::Const(0)).unwrap(),
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
        let cs_ta = ACSThresholdAutomaton::new(interval_ta);
        let var_x = cs_ta.idx_ctx.to_cs_var(&Variable::new("x"));
        let var_y = cs_ta.idx_ctx.to_cs_var(&Variable::new("y"));

        let mut interval_state = ACSIntervalState::new_cfg_all_zero_interval(&cs_ta);
        interval_state[var_x] = ACSInterval(1);
        interval_state[var_y] = ACSInterval(0);

        let rule = CSRule {
            id: 0,
            source: ACSLocation(0),
            target: ACSLocation(1),
            guard: CSIntervalConstraint::True,
            actions: vec![CSIntervalAction {
                var: var_x,
                effect: IntervalActionEffect::Reset,
            }],
        };

        let config = ACSTAConfig {
            loc_state: ACSLocState {
                loc_state: vec![0, 1, 0],
            },
            interval_state: interval_state.clone(),
        };

        let got_pred = config.compute_potential_predecessors(&rule, &cs_ta);
        assert!(got_pred.is_none())
    }

    #[test]
    fn test_castaconfig_from_disjunct_target() {
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
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(2)),
                    ))
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
        let cs_ta = ACSThresholdAutomaton::new(interval_ta);
        let loc_l2 = cs_ta.idx_ctx.to_cs_loc(&Location::new("l2"));
        let loc_l3 = cs_ta.idx_ctx.to_cs_loc(&Location::new("l3"));

        let target_1 = UpwardsClosedSet::new_cover([Location::new("l3")]);
        let target_2 = UpwardsClosedSet::new_cover([Location::new("l2")]);
        let disj = target_1 | target_2;

        let got_configs = ACSTAConfig::from_disjunct_target(&disj, &cs_ta).collect::<HashSet<_>>();

        let interval_states = ACSIntervalState::all_possible_interval_configs(&cs_ta);
        let configs_l2 = interval_states.iter().map(|is| {
            let mut loc_state = ACSLocState::new_all_zero(&cs_ta);
            loc_state[loc_l2] = 1;

            ACSTAConfig {
                loc_state,
                interval_state: is.clone(),
            }
        });
        let configs_l3 = interval_states.iter().map(|is| {
            let mut loc_state = ACSLocState::new_all_zero(&cs_ta);
            loc_state[loc_l3] = 1;

            ACSTAConfig {
                loc_state,
                interval_state: is.clone(),
            }
        });
        let expected_configs = configs_l2.chain(configs_l3).collect::<HashSet<_>>();

        assert_eq!(got_configs, expected_configs)
    }

    #[test]
    fn test_castaconfig_from_disjunct_target_with_var_constr() {
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
                        ComparisonOp::Geq,
                        Box::new(IntegerExpression::Const(3)),
                    ))
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

        let cs_ta = ACSThresholdAutomaton::new(interval_ta);
        let loc_l2 = cs_ta.idx_ctx.to_cs_loc(&Location::new("l2"));
        let loc_l3 = cs_ta.idx_ctx.to_cs_loc(&Location::new("l3"));

        let cstr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Variable::new("x"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        );

        // l3 > 1 && x == 0
        let target_1 = UpwardsClosedSet::new_var_constraint(cstr.clone().try_into().unwrap())
            & UpwardsClosedSet::new_cover_int([(Location::new("l3"), 1)]);

        // x == 0
        let target_2 = UpwardsClosedSet::new_var_constraint(cstr.clone().try_into().unwrap())
            & UpwardsClosedSet::new_cover_int([(Location::new("l2"), 1)]);
        let disj = target_1 | target_2;

        let got_configs = ACSTAConfig::from_disjunct_target(&disj, &cs_ta).collect::<HashSet<_>>();

        let interval_state = ACSIntervalState::new_cfg_all_zero_interval(&cs_ta);
        let mut state2 = interval_state.clone();
        state2[cs_ta.to_cs_var(&Variable::new("y"))] = ACSInterval(1);

        let interval_states = [interval_state, state2];
        let configs_l2 = interval_states.iter().map(|is| {
            let mut loc_state = ACSLocState::new_all_zero(&cs_ta);
            loc_state[loc_l2] = 1;

            ACSTAConfig {
                loc_state,
                interval_state: is.clone(),
            }
        });
        let configs_l3 = interval_states.iter().map(|is| {
            let mut loc_state = ACSLocState::new_all_zero(&cs_ta);
            loc_state[loc_l3] = 1;

            ACSTAConfig {
                loc_state,
                interval_state: is.clone(),
            }
        });
        let expected_configs = configs_l2.chain(configs_l3).collect::<HashSet<_>>();

        assert_eq!(
            got_configs,
            expected_configs,
            "Got: {}\nExpected: {}\n",
            join_iterator(got_configs.iter().map(|c| c.display(&cs_ta)), "; "),
            join_iterator(expected_configs.iter().map(|c| c.display(&cs_ta)), "; ")
        )
    }

    #[test]
    fn test_cstaconfig_partial_order() {
        let config1 = ACSTAConfig {
            loc_state: ACSLocState {
                loc_state: vec![1, 2, 3],
            },
            interval_state: ACSIntervalState {
                v_to_interval: vec![ACSInterval(3), ACSInterval(2), ACSInterval(1)],
            },
        };
        let config2 = ACSTAConfig {
            loc_state: ACSLocState {
                loc_state: vec![2, 2, 4],
            },
            interval_state: ACSIntervalState {
                v_to_interval: vec![ACSInterval(3), ACSInterval(2), ACSInterval(1)],
            },
        };

        assert_eq!(config1.part_cmp(&config1), PartialOrdCompResult::Equal);
        assert_eq!(config1.part_cmp(&config2), PartialOrdCompResult::Smaller);
        assert_eq!(config2.part_cmp(&config1), PartialOrdCompResult::Greater);

        let config3 = ACSTAConfig {
            loc_state: ACSLocState {
                loc_state: vec![0, 2, 6],
            },
            interval_state: ACSIntervalState {
                v_to_interval: vec![ACSInterval(3), ACSInterval(2), ACSInterval(1)],
            },
        };
        assert_eq!(
            config1.part_cmp(&config3),
            PartialOrdCompResult::Incomparable
        );
        assert_eq!(
            config3.part_cmp(&config1),
            PartialOrdCompResult::Incomparable
        );

        let config4 = ACSTAConfig {
            loc_state: ACSLocState {
                loc_state: vec![1, 2, 3],
            },
            interval_state: ACSIntervalState {
                v_to_interval: vec![ACSInterval(0), ACSInterval(2), ACSInterval(1)],
            },
        };
        assert_eq!(
            config1.part_cmp(&config4),
            PartialOrdCompResult::Incomparable
        );
        assert_eq!(
            config4.part_cmp(&config1),
            PartialOrdCompResult::Incomparable
        );
    }

    #[test]
    fn test_cstaconfig_display() {
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
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(2)),
                    ))
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
        let ta = ACSThresholdAutomaton::new(interval_ta);

        let var_x = ta.idx_ctx.to_cs_var(&Variable::new("x"));

        let mut interval_state = ACSIntervalState::new_cfg_all_zero_interval(&ta);
        interval_state[var_x] = ACSInterval(3);

        let loc_l3 = ta.idx_ctx.to_cs_loc(&Location::new("l3"));
        let loc_l2 = ta.idx_ctx.to_cs_loc(&Location::new("l2"));

        let mut loc_state = ACSLocState::new_all_zero(&ta);
        loc_state[loc_l2] = 1;
        loc_state[loc_l3] = 42;

        let config = ACSTAConfig {
            loc_state,
            interval_state,
        };

        let got_string = config.display(&ta);
        let expected_string =
            "locations: (l1 : 0, l2 : 1, l3 : 42), variables: (x : ]2, ∞[, y : [0, 1[)";

        assert_eq!(&got_string, expected_string);
    }

    #[test]
    fn test_cstaconfig_display_compact() {
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
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(2)),
                    ))
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
        let ta = ACSThresholdAutomaton::new(interval_ta);

        let var_x = ta.idx_ctx.to_cs_var(&Variable::new("x"));

        let mut interval_state = ACSIntervalState::new_cfg_all_zero_interval(&ta);
        interval_state[var_x] = ACSInterval(3);

        let loc_l3 = ta.idx_ctx.to_cs_loc(&Location::new("l3"));
        let loc_l2 = ta.idx_ctx.to_cs_loc(&Location::new("l2"));

        let mut loc_state = ACSLocState::new_all_zero(&ta);
        loc_state[loc_l2] = 1;
        loc_state[loc_l3] = 42;

        let config = ACSTAConfig {
            loc_state,
            interval_state,
        };

        let got_string = config.display_compact(&ta);
        let expected_string = "locations: (l2 : 1, l3 : 42), variables: (x : ]2, ∞[)";

        assert_eq!(&got_string, expected_string);
    }

    #[test]
    fn test_interval_state_getters() {
        let mut interval_state = ACSIntervalState {
            v_to_interval: vec![ACSInterval(0), ACSInterval(1), ACSInterval(2)],
        };

        let var_to_interval = interval_state
            .into_iterator_variable_interval()
            .collect::<HashMap<_, _>>();

        assert_eq!(
            var_to_interval,
            HashMap::from([
                (CSVariable(0), ACSInterval(0)),
                (CSVariable(1), ACSInterval(1)),
                (CSVariable(2), ACSInterval(2))
            ])
        );

        assert_eq!(interval_state[CSVariable(1)], ACSInterval(1));
        assert_eq!(interval_state[&CSVariable(1)], ACSInterval(1));

        interval_state[CSVariable(1)] = ACSInterval(0);
        assert_eq!(interval_state[CSVariable(1)], ACSInterval(0));
        assert_eq!(interval_state[&CSVariable(1)], ACSInterval(0));
    }

    #[test]
    fn test_interval_state_partial_order() {
        let interval_state1 = ACSIntervalState {
            v_to_interval: vec![ACSInterval(0), ACSInterval(1), ACSInterval(2)],
        };
        let interval_state2 = ACSIntervalState {
            v_to_interval: vec![ACSInterval(0), ACSInterval(2), ACSInterval(2)],
        };

        assert_eq!(
            interval_state1.part_cmp(&interval_state1),
            PartialOrdCompResult::Equal
        );

        assert_eq!(
            interval_state1.part_cmp(&interval_state2),
            PartialOrdCompResult::Incomparable
        );
        assert_eq!(
            interval_state2.part_cmp(&interval_state1),
            PartialOrdCompResult::Incomparable
        );
    }

    #[test]
    fn test_interval_state_all_possible_interval_configs() {
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
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(2)),
                    ))
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
        let cs_ta = ACSThresholdAutomaton::new(interval_ta);
        let var_x = cs_ta.idx_ctx.to_cs_var(&Variable::new("x"));
        let var_y = cs_ta.idx_ctx.to_cs_var(&Variable::new("y"));

        let interval_state = ACSIntervalState::new_cfg_all_zero_interval(&cs_ta);

        // x: [0,1[ [1, 2[ [2,2] ]2,...
        let got_states = ACSIntervalState::all_possible_interval_configs(&cs_ta);

        let mut state1 = interval_state.clone();
        state1[var_x] = ACSInterval(1);

        let mut state2 = interval_state.clone();
        state2[var_x] = ACSInterval(2);

        let mut state6 = interval_state.clone();
        state6[var_x] = ACSInterval(3);

        let mut state3 = interval_state.clone();
        state3[var_y] = ACSInterval(1);

        let mut state4 = interval_state.clone();
        state4[var_x] = ACSInterval(1);
        state4[var_y] = ACSInterval(1);

        let mut state5 = interval_state.clone();
        state5[var_x] = ACSInterval(2);
        state5[var_y] = ACSInterval(1);

        let mut state7 = interval_state.clone();
        state7[var_x] = ACSInterval(3);
        state7[var_y] = ACSInterval(1);

        let expected_states = HashSet::from([
            interval_state.clone(),
            state1,
            state2,
            state3,
            state4,
            state5,
            state6,
            state7,
        ]);
        assert_eq!(
            got_states.into_iter().collect::<HashSet<_>>(),
            expected_states
        );
    }

    #[test]
    fn test_interval_state_all_possible_interval_configs_true() {
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
                        ComparisonOp::Geq,
                        Box::new(IntegerExpression::Const(3)),
                    ))
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
        let cs_ta = ACSThresholdAutomaton::new(interval_ta);
        let var_x = cs_ta.idx_ctx.to_cs_var(&Variable::new("x"));
        let var_y = cs_ta.idx_ctx.to_cs_var(&Variable::new("y"));

        let interval_state = ACSIntervalState::new_cfg_all_zero_interval(&cs_ta);

        let cstr = IntervalConstraint::True;

        let got_states = ACSIntervalState::get_target_interval_configs(cstr, &cs_ta);

        let mut state1 = interval_state.clone();
        state1[var_x] = ACSInterval(1);

        let mut state2 = interval_state.clone();
        state2[var_x] = ACSInterval(2);

        let mut state3 = interval_state.clone();
        state3[var_y] = ACSInterval(1);

        let mut state4 = interval_state.clone();
        state4[var_x] = ACSInterval(1);
        state4[var_y] = ACSInterval(1);

        let mut state5 = interval_state.clone();
        state5[var_x] = ACSInterval(2);
        state5[var_y] = ACSInterval(1);

        let expected_states = HashSet::from([
            interval_state.clone(),
            state1,
            state2,
            state3,
            state4,
            state5,
        ]);
        assert_eq!(
            got_states.into_iter().collect::<HashSet<_>>(),
            expected_states
        );
    }

    #[test]
    fn test_target_interval_configs() {
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
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(2)),
                    ))
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
        let cs_ta = ACSThresholdAutomaton::new(interval_ta);
        let var_y = cs_ta.idx_ctx.to_cs_var(&Variable::new("y"));

        let cstr = IntervalConstraint::SingleVarIntervalConstr(
            Variable::new("x"),
            vec![Interval::new_constant(0, 1)],
        );
        let got_states = ACSIntervalState::get_target_interval_configs(cstr, &cs_ta);

        let interval_state = ACSIntervalState::new_cfg_all_zero_interval(&cs_ta);
        let mut state2 = interval_state.clone();
        state2[var_y] = ACSInterval(1);

        let expected_states = HashSet::from([interval_state.clone(), state2]);
        assert_eq!(
            got_states.into_iter().collect::<HashSet<_>>(),
            expected_states
        );
    }

    #[test]
    fn test_interval_state_compute_all_predecessor_configs() {
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
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(2)),
                    ))
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
        let cs_ta = ACSThresholdAutomaton::new(interval_ta);

        let var_x = cs_ta.idx_ctx.to_cs_var(&Variable::new("x"));
        let var_y = cs_ta.idx_ctx.to_cs_var(&Variable::new("y"));

        // all zero -> no predecessor because no inc possible
        let interval_state = ACSIntervalState::new_cfg_all_zero_interval(&cs_ta);
        let rule = CSRule {
            id: 0,
            source: ACSLocation(0),
            target: ACSLocation(1),
            guard: CSIntervalConstraint::True,
            actions: vec![CSIntervalAction {
                var: var_x,
                effect: IntervalActionEffect::Inc(1),
            }],
        };
        let got_preds = interval_state.compute_all_predecessor_configs(&rule, &cs_ta);
        let expected_preds = HashSet::from([]);
        assert_eq!(
            got_preds.into_iter().collect::<HashSet<_>>(),
            expected_preds
        );

        // Interval state: x [2,2], y: [0,1]
        let mut is_exact_int = ACSIntervalState::new_cfg_all_zero_interval(&cs_ta);
        is_exact_int[var_x] = ACSInterval(2); // 2,2
        is_exact_int[var_y] = ACSInterval(0);

        let mut is_open_int = ACSIntervalState::new_cfg_all_zero_interval(&cs_ta);
        is_open_int[var_x] = ACSInterval(3); // 2,\infty
        is_open_int[var_y] = ACSInterval(0);

        let rule = CSRule {
            id: 0,
            source: ACSLocation(0),
            target: ACSLocation(1),
            guard: CSIntervalConstraint::True,
            actions: vec![CSIntervalAction {
                var: var_x,
                effect: IntervalActionEffect::Inc(1),
            }],
        };

        let got_preds_exact = is_exact_int.compute_all_predecessor_configs(&rule, &cs_ta);

        let mut pred_1 = is_exact_int.clone();
        pred_1[var_x] = ACSInterval(1);

        let expected_preds_exact = HashSet::from([
            // previous interval
            pred_1.clone(),
        ]);
        assert_eq!(
            got_preds_exact.clone().into_iter().collect::<HashSet<_>>(),
            expected_preds_exact,
            "Got: {}\nExpected: {}",
            join_iterator(got_preds_exact.iter().map(|c| c.display(&cs_ta)), ";"),
            join_iterator(expected_preds_exact.iter().map(|c| c.display(&cs_ta)), ";"),
        );

        let got_preds_open = is_open_int.compute_all_predecessor_configs(&rule, &cs_ta);
        let expected_preds_open = HashSet::from([
            is_open_int.clone(),
            // previous interval
            is_exact_int.clone(),
        ]);
        assert_eq!(
            got_preds_open.clone().into_iter().collect::<HashSet<_>>(),
            expected_preds_open,
            "Got: {}\nExpected: {}",
            join_iterator(got_preds_open.iter().map(|c| c.display(&cs_ta)), ";"),
            join_iterator(expected_preds_open.iter().map(|c| c.display(&cs_ta)), ";"),
        );

        let rule = CSRule {
            id: 0,
            source: ACSLocation(0),
            target: ACSLocation(1),
            guard: CSIntervalConstraint::True,
            actions: vec![CSIntervalAction {
                var: var_x,
                effect: IntervalActionEffect::Dec(1),
            }],
        };

        let got_preds = is_open_int.compute_all_predecessor_configs(&rule, &cs_ta);

        let mut pred_1 = is_open_int.clone();
        pred_1[var_x] = ACSInterval(3);
        let expected_preds = HashSet::from([pred_1.clone()]);
        assert_eq!(
            got_preds.into_iter().collect::<HashSet<_>>(),
            expected_preds
        );

        let rule = CSRule {
            id: 0,
            source: ACSLocation(0),
            target: ACSLocation(1),
            guard: CSIntervalConstraint::True,
            actions: vec![CSIntervalAction {
                var: var_y,
                effect: IntervalActionEffect::Reset,
            }],
        };

        let got_preds = is_open_int.compute_all_predecessor_configs(&rule, &cs_ta);
        let mut pred_1 = is_open_int.clone();
        pred_1[var_y] = ACSInterval(1);
        let expected_preds = HashSet::from([is_open_int.clone(), pred_1]);
        assert_eq!(
            got_preds.into_iter().collect::<HashSet<_>>(),
            expected_preds
        );
        assert_eq!(cs_ta.get_all_intervals(&var_x).count(), 4);
    }

    #[test]
    fn test_interval_state_display() {
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
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(2)),
                    ))
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
        let ta = ACSThresholdAutomaton::new(interval_ta);

        let var_x = ta.idx_ctx.to_cs_var(&Variable::new("x"));

        let mut interval_state = ACSIntervalState::new_cfg_all_zero_interval(&ta);
        interval_state[var_x] = ACSInterval(3);

        let got_string = interval_state.display(&ta);
        let expected_string = "x : ]2, ∞[, y : [0, 1[";

        assert_eq!(&got_string, expected_string);
    }

    #[test]
    fn test_interval_state_display_compact() {
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
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(2)),
                    ))
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
        let ta = ACSThresholdAutomaton::new(interval_ta);

        let var_x = ta.idx_ctx.to_cs_var(&Variable::new("x"));

        let mut interval_state = ACSIntervalState::new_cfg_all_zero_interval(&ta);
        interval_state[var_x] = ACSInterval(2);

        let got_string = interval_state.display_compact(&ta);
        let expected_string = "x : [2, 2]";

        assert_eq!(&got_string, expected_string);
    }

    #[test]
    fn test_loc_state_getters() {
        let mut loc_state = ACSLocState {
            loc_state: vec![1, 2, 3, 4, 5],
        };

        let state_n = loc_state
            .into_iterator_loc_n_procs()
            .collect::<HashMap<_, _>>();

        assert_eq!(
            state_n,
            HashMap::from([
                (ACSLocation(0), 1),
                (ACSLocation(1), 2),
                (ACSLocation(2), 3),
                (ACSLocation(3), 4),
                (ACSLocation(4), 5)
            ])
        );

        assert_eq!(loc_state[ACSLocation(1)], 2);
        assert_eq!(loc_state[&ACSLocation(1)], 2);

        loc_state[ACSLocation(0)] += 1;
        assert_eq!(loc_state[ACSLocation(0)], 2);
    }

    #[test]
    fn test_loc_state_part_ord() {
        let loc_state1 = ACSLocState {
            loc_state: vec![1, 2, 3, 4, 5],
        };

        let loc_state2 = ACSLocState {
            loc_state: vec![1, 2, 3, 5, 5],
        };

        assert_eq!(
            loc_state1.part_cmp(&loc_state2),
            PartialOrdCompResult::Smaller
        );
        assert_eq!(
            loc_state2.part_cmp(&loc_state1),
            PartialOrdCompResult::Greater
        );
        assert_eq!(
            loc_state1.part_cmp(&loc_state1),
            PartialOrdCompResult::Equal
        );

        let loc_state3 = ACSLocState {
            loc_state: vec![1, 2, 3, 0, 6],
        };

        assert_eq!(
            loc_state1.part_cmp(&loc_state3),
            PartialOrdCompResult::Incomparable
        );

        let loc_state4 = ACSLocState {
            loc_state: vec![1, 2, 3, 6, 0],
        };

        assert_eq!(
            loc_state1.part_cmp(&loc_state4),
            PartialOrdCompResult::Incomparable
        );
    }

    #[test]
    fn test_loc_state_compute_predecessor_min_basis() {
        let loc_state = ACSLocState {
            loc_state: vec![0, 1, 2],
        };

        let rule = CSRule {
            id: 0,
            source: ACSLocation(0),
            target: ACSLocation(1),
            guard: CSIntervalConstraint::True,
            actions: vec![],
        };

        let pred = loc_state.compute_predecessors_min_basis(&rule);

        let expected_pred = ACSLocState {
            loc_state: vec![1, 0, 2],
        };

        assert_eq!(pred, expected_pred);

        let loc_state = ACSLocState {
            loc_state: vec![0, 0, 2],
        };

        let rule = CSRule {
            id: 0,
            source: ACSLocation(0),
            target: ACSLocation(1),
            guard: CSIntervalConstraint::True,
            actions: vec![],
        };

        let pred = loc_state.compute_predecessors_min_basis(&rule);

        let expected_pred = ACSLocState {
            loc_state: vec![1, 0, 2],
        };

        assert_eq!(pred, expected_pred);
    }

    #[test]
    fn test_loc_state_compute_target_cfg() {
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
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(2)),
                    ))
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
        let cs_ta = ACSThresholdAutomaton::new(interval_ta);

        // Cover l3
        let spec = UpwardsClosedSet::new_cover([Location::new("l3")]);
        let spec = spec.upwards_closed_clauses().next().unwrap();
        let got_loc_state = ACSLocState::compute_target_cfg(spec, &cs_ta);

        let cs_loc = cs_ta.idx_ctx.to_cs_loc(&Location::new("l3"));
        let mut expected_loc_state = ACSLocState {
            loc_state: vec![0, 0, 0],
        };
        expected_loc_state[cs_loc] = 1;

        assert_eq!(got_loc_state, expected_loc_state);

        // Cover l1
        let spec = UpwardsClosedSet::new_cover([Location::new("l1")]);
        let spec = spec.upwards_closed_clauses().next().unwrap();
        let got_loc_state = ACSLocState::compute_target_cfg(spec, &cs_ta);

        let loc_l1 = cs_ta.idx_ctx.to_cs_loc(&Location::new("l1"));
        let mut expected_loc_state = ACSLocState {
            loc_state: vec![0, 0, 0],
        };
        expected_loc_state[loc_l1] = 1;
        assert_eq!(got_loc_state, expected_loc_state);

        // Cover l1 + l2
        let spec = UpwardsClosedSet::new_cover([Location::new("l1"), Location::new("l2")]);
        let spec = spec.upwards_closed_clauses().next().unwrap();
        let got_loc_state = ACSLocState::compute_target_cfg(spec, &cs_ta);

        let mut expected_loc_state = ACSLocState {
            loc_state: vec![0, 0, 0],
        };
        let cs_loc1 = cs_ta.idx_ctx.to_cs_loc(&Location::new("l1"));
        expected_loc_state[cs_loc1] = 1;
        let cs_loc2 = cs_ta.idx_ctx.to_cs_loc(&Location::new("l2"));
        expected_loc_state[cs_loc2] = 1;

        assert_eq!(got_loc_state, expected_loc_state);

        // Cover l1 + l2 + l3
        let spec = UpwardsClosedSet::new_cover([
            Location::new("l1"),
            Location::new("l2"),
            Location::new("l3"),
        ]);
        let spec = spec.upwards_closed_clauses().next().unwrap();
        let got_loc_state = ACSLocState::compute_target_cfg(spec, &cs_ta);

        let expected_loc_state = ACSLocState {
            loc_state: vec![1, 1, 1],
        };

        assert_eq!(got_loc_state, expected_loc_state);

        // GeneralCover l3
        let spec = UpwardsClosedSet::new_cover_int([(Location::new("l3"), 42)]);
        let spec = spec.upwards_closed_clauses().next().unwrap();
        let got_loc_state = ACSLocState::compute_target_cfg(spec, &cs_ta);

        let cs_loc = cs_ta.idx_ctx.to_cs_loc(&Location::new("l3"));
        let mut expected_loc_state = ACSLocState {
            loc_state: vec![0, 0, 0],
        };
        expected_loc_state[cs_loc] = 42;

        assert_eq!(got_loc_state, expected_loc_state);

        // GeneralCover l1 + l2 + l3
        let spec = UpwardsClosedSet::new_cover_int([
            (Location::new("l1"), 42),
            (Location::new("l2"), 42),
            (Location::new("l3"), 42),
        ]);
        let spec = spec.upwards_closed_clauses().next().unwrap();
        let got_loc_state = ACSLocState::compute_target_cfg(spec, &cs_ta);

        let expected_loc_state = ACSLocState {
            loc_state: vec![42, 42, 42],
        };

        assert_eq!(got_loc_state, expected_loc_state);
    }

    #[test]
    fn test_loc_state_display() {
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
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(2)),
                    ))
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
        let ta = ACSThresholdAutomaton::new(interval_ta);

        let loc_l3 = ta.idx_ctx.to_cs_loc(&Location::new("l3"));
        let loc_l2 = ta.idx_ctx.to_cs_loc(&Location::new("l2"));

        let mut loc_state = ACSLocState::new_all_zero(&ta);
        loc_state[loc_l2] = 1;
        loc_state[loc_l3] = 42;

        let got_string = loc_state.display(&ta);
        let expected_string = "l1 : 0, l2 : 1, l3 : 42";

        assert_eq!(&got_string, expected_string);
    }

    #[test]
    fn test_loc_state_display_compact() {
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
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(2)),
                    ))
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
        let ta = ACSThresholdAutomaton::new(interval_ta);

        let loc_l3 = ta.idx_ctx.to_cs_loc(&Location::new("l3"));
        let loc_l2 = ta.idx_ctx.to_cs_loc(&Location::new("l2"));

        let mut loc_state = ACSLocState::new_all_zero(&ta);
        loc_state[loc_l2] = 1;
        loc_state[loc_l3] = 42;

        let got_string = loc_state.display_compact(&ta);
        let expected_string = "l2 : 1, l3 : 42";

        assert_eq!(&got_string, expected_string);
    }
}
