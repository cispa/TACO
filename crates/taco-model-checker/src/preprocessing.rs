//! Preprocessing for threshold automata
//!
//! This module contains the logic for preprocessing threshold automata.
//! The goal of this preprocessing is to simplify the threshold automaton, such
//! that the threshold automaton is easier to analyze.
//!
//! The following preprocessors are implemented:
//! - [DropSelfLoops]: Removes self loops from the threshold automaton if the
//!   transition rule has no effect on the shared variables.
//! - [DropUnreachableLocations]: Removes unreachable locations from the
//!   threshold automaton.
//! - [ReplaceTrivialGuardsStatic]: Replaces some frequently generated guards
//!   that are always enabled with true.
//! - [ReplaceTrivialGuardsSMT]: Replaces guards which are always satisfied, uses
//!   SMT to determine which guards are always satisfied.
//! - [CollapseLocations]: Collapse locations which have the same incoming rules
//! - [DropUnsatisfiableRules]: Removes rules where the guards are
//!   unsatisfiable.
//! - [CheckInitCondSatSMT]: Checks whether the initial condition of a threshold
//!   automaton are satisfiable, if not, removes all rules, locations and adds
//!   false to the initial locations.

use log::{debug, info, trace};

#[cfg(feature = "config_deserialize")]
use serde::Deserialize;

use std::{
    collections::{BTreeSet, HashMap, HashSet},
    fmt::{self},
};

use taco_smt_encoder::{
    ProvidesSMTSolverBuilder, SMTSolverBuilder, SMTSolverContext,
    expression_encoding::{
        EncodeToSMT, SMTVariableContext, StaticSMTContext,
        ta_encoding::{encode_initial_constraints, encode_resilience_condition},
    },
};
use taco_threshold_automaton::{
    ActionDefinition, ModifiableThresholdAutomaton, RuleDefinition, ThresholdAutomaton,
    VariableConstraint,
    expressions::{
        Atomic, BooleanConnective, BooleanExpression, ComparisonOp, IntegerExpression, Location,
        Variable,
    },
    general_threshold_automaton::{GeneralThresholdAutomaton, Rule},
};

use crate::{ModelCheckerContext, TASpecification};

/// Trait for preprocessing threshold automata
///
/// This trait is implemented by types that can process a threshold automaton
/// to simplify it for further analysis.
pub trait Preprocessor<
    T: ModifiableThresholdAutomaton + ThresholdAutomaton,
    S: TASpecification,
    C: ModelCheckerContext,
>
{
    /// Process the threshold automaton and attempt to simplify it
    fn process(&self, ta: &mut T, spec: &S, ctx: &C);
}

/// Preprocessor that drops self loops from the threshold automaton if the
/// transition rule has no effect on the shared variables
///
/// This threshold automaton preprocessor removes self loops from the threshold
/// automaton if the transition rule has no effect on the shared variables.
///
/// Such a self loop does not change the location of any process, nor does it
/// change the valuations of any shared variables. Therefore, it can be safely
/// removed from the threshold automaton.
pub struct DropSelfLoops {}

impl Default for DropSelfLoops {
    fn default() -> Self {
        Self::new()
    }
}

impl DropSelfLoops {
    /// Create a new instance of the `DropSelfLoop` preprocessor
    pub fn new() -> Self {
        Self {}
    }
}

impl<T: ModifiableThresholdAutomaton, S: TASpecification, C: ModelCheckerContext>
    Preprocessor<T, S, C> for DropSelfLoops
{
    fn process(&self, ta: &mut T, _spec: &S, _ctx: &C) {
        let n_rules = ta.rules().count();

        ta.retain_rules(|rule| {
            rule.source() != rule.target() || rule.actions().any(|action| !action.is_unchanged())
        });

        info!(
            "Preprocessor 'DropSelfLoops' on '{}' removed {} of {} rules: Removed rules are self-loops that do not update any shared variable.",
            ta.name(),
            n_rules - ta.rules().count(),
            n_rules
        );
    }
}

/// Preprocessor that drops unreachable locations from the threshold automaton
///
/// This preprocessor constructs the underlying graph of the threshold automaton
/// without considering the guards of the transition rules.
///
/// It then performs a reachability analysis to determine the reachable
/// locations. If a location is not reachable, i.e. it is not reachable through
/// any transition and not initial, it is removed from the threshold automaton.
/// If there are any outgoing rules, they are also removed from the threshold
/// automaton.
///
/// This step should generally be applied, when rules have been removed from the
/// threshold automaton, or if locations are no longer considered to be initial.
#[derive(Default)]
pub struct DropUnreachableLocations {}

impl DropUnreachableLocations {
    /// Create a new instance of the `DropUnreachableLocations` preprocessor
    pub fn new() -> Self {
        Self {}
    }

    /// Compute the set of unreachable locations in the threshold automaton
    fn compute_unreachable_locations<T: ThresholdAutomaton>(
        &self,
        ta: &T,
        locs_to_keep: HashSet<&Location>,
    ) -> HashSet<Location> {
        let mut reached = ta
            .locations()
            .filter(|loc| ta.can_be_initial_location(loc))
            .collect::<HashSet<_>>();

        let mut found_new_loc = true;
        while found_new_loc {
            found_new_loc = false;

            for rule in ta.rules() {
                if reached.contains(&rule.source()) && !reached.contains(&rule.target()) {
                    reached.insert(rule.target());
                    found_new_loc = true;
                }
            }
        }

        ta.locations()
            .filter(|loc| !reached.contains(loc) && !locs_to_keep.contains(loc))
            .filter(|loc| {
                !ta.initial_location_constraints().any(|ic| {
                    ic.contains_atom_a(loc) && !ic.try_check_expr_constraints_to_zero(loc)
                })
            })
            .cloned()
            .collect::<HashSet<_>>()
    }
}

impl<S: TASpecification, C: ModelCheckerContext> Preprocessor<GeneralThresholdAutomaton, S, C>
    for DropUnreachableLocations
{
    /// Preprocessor that drops unreachable locations from the threshold automaton
    ///
    /// This preprocessing step constructs the graph of the threshold automaton
    /// without considering the guards of the transition rules.
    ///
    /// It then performs a reachability analysis to determine the reachable
    /// locations. If a location is not reachable, it is removed from the threshold
    /// automaton.
    fn process(&self, ta: &mut GeneralThresholdAutomaton, spec: &S, _ctx: &C) {
        let locations_to_keep = spec.locs_appearing().into_iter().collect();

        let unreachable_locations = self.compute_unreachable_locations(ta, locations_to_keep);
        if unreachable_locations.is_empty() {
            debug!("Preprocessor 'DropUnreachableLocations' did not find locations to remove.");
            return;
        }

        let n_locations = ta.locations().count();
        let n_rules = ta.rules().count();

        for loc in unreachable_locations {
            ta.remove_location_and_replace_with(&loc, IntegerExpression::Const(0));
        }

        info!(
            "Preprocessor 'DropUnreachableLocations' on '{}' removed {} of {} locations and {} of {} rules: Removed locations were unreachable in the underlying graph of the threshold automaton.",
            ta.name(),
            n_locations - ta.locations().count(),
            n_locations,
            n_rules - ta.rules().count(),
            n_rules
        );
    }
}

/// A lot of automatically generated benchmarks have guards of the form
/// `(var1 >= 1 || var1 == 0)`  or `var >= 0`  which are satisfied. This
/// preprocessor replaces these guards with `true`.
///
/// This preprocessor only checks for a few trivial patterns, if you want a
/// more general preprocessor use [`ReplaceTrivialGuardsSMT`].
///
/// **Note**: If you assume variables can have values smaller than 0 this
/// preprocessor should not be used!
pub struct ReplaceTrivialGuardsStatic {}

impl Default for ReplaceTrivialGuardsStatic {
    fn default() -> Self {
        Self::new()
    }
}

impl ReplaceTrivialGuardsStatic {
    ///? Can we generalize this to more expressions ?
    fn is_trivially_true<T: Atomic>(expr: &BooleanExpression<T>) -> bool {
        match expr {
            // var == 0 || var >= 1
            BooleanExpression::BinaryExpression(lhs, BooleanConnective::Or, rhs) => {
                match (lhs.as_ref(), rhs.as_ref()) {
                    (
                        BooleanExpression::ComparisonExpression(expr_r, ComparisonOp::Eq, c_r),
                        BooleanExpression::ComparisonExpression(expr_l, ComparisonOp::Geq, c_l),
                    )
                    | (
                        BooleanExpression::ComparisonExpression(expr_l, ComparisonOp::Geq, c_l),
                        BooleanExpression::ComparisonExpression(expr_r, ComparisonOp::Eq, c_r),
                    ) => {
                        if c_l.as_ref().try_to_evaluate_to_const() == Option::Some(1)
                            && c_r.as_ref().try_to_evaluate_to_const() == Option::Some(0)
                        {
                            return expr_l == expr_r;
                        }
                        false
                    }
                    _ => false,
                }
            }
            // var >= 0
            BooleanExpression::ComparisonExpression(_, ComparisonOp::Geq, rhs)
            | BooleanExpression::ComparisonExpression(rhs, ComparisonOp::Leq, _) => {
                if rhs.try_to_evaluate_to_const() == Option::Some(0) {
                    return true;
                }
                false
            }
            _ => false,
        }
    }

    /// Replace trivial boolean expressions with `true`
    ///
    /// **Note**: If you assume variables can have values smaller than 0 this
    /// preprocessor should not be used!
    fn replace_trivial_boolean_expr<T: Atomic>(expr: &mut BooleanExpression<T>) {
        if Self::is_trivially_true(expr) {
            *expr = BooleanExpression::True;
            return;
        }

        match expr {
            BooleanExpression::ComparisonExpression(_, _, _) => (),
            BooleanExpression::BinaryExpression(lhs, _, rhs) => {
                Self::replace_trivial_boolean_expr(lhs.as_mut());
                Self::replace_trivial_boolean_expr(rhs.as_mut());
            }
            BooleanExpression::Not(expr) => Self::replace_trivial_boolean_expr(expr.as_mut()),
            BooleanExpression::True => (),
            BooleanExpression::False => (),
        }
    }

    /// Create a new instance of the [`ReplaceTrivialGuardsStatic`] preprocessor
    pub fn new() -> Self {
        Self {}
    }
}

impl<S: TASpecification, C: ModelCheckerContext> Preprocessor<GeneralThresholdAutomaton, S, C>
    for ReplaceTrivialGuardsStatic
{
    /// A lot of automatically generated benchmarks have guards of the form
    /// `(var1 >= 1 || var1 == 0)`  or `var >= 0`  which are satisfied. This
    /// preprocessor replaces these guards with `true`.
    ///
    /// This preprocessor only checks for a few trivial patterns, if you want a
    /// more general preprocessor use [`ReplaceTrivialGuardsSMT`].
    ///
    /// **Note**: If you assume variables can have values smaller than 0 this
    /// preprocessor should not be used!
    fn process(&self, ta: &mut GeneralThresholdAutomaton, _spec: &S, _ctx: &C) {
        ta.transform_rules(|rule| {
            rule.transform_guard(Self::replace_trivial_boolean_expr);
        });
    }
}

/// Preprocessor that checks for trivial guards using an SMT solver
///
/// This preprocessor replaces guards that are always satisfied with `true`. To
/// do this, it uses an SMT solver to check whether the negation of the guard
/// can be satisfied. If this is not possible, the guard is replaced with
/// `true`.
///
/// This preprocessor can be very useful for automatically generated benchmarks
/// where guards are often not meaningful. However, these checks can be very
/// expensive. A more light weight preprocessor is
/// [`ReplaceTrivialGuardsStatic`], but it is not complete.
///
/// **Note**: If you assume variables can have values smaller than 0 this
/// preprocessor should not be used!
pub struct ReplaceTrivialGuardsSMT {}

impl Default for ReplaceTrivialGuardsSMT {
    fn default() -> Self {
        Self::new()
    }
}

impl ReplaceTrivialGuardsSMT {
    /// Create a new instance of the preprocessor [`ReplaceTrivialGuardsSMT`]
    pub fn new() -> Self {
        Self {}
    }

    /// Checks if a boolean expression is trivially true using an smt solver
    ///
    /// Returns true if the expression is trivially true, false otherwise.
    fn is_trivially_true(expr: &BooleanExpression<Variable>, ctx: &mut StaticSMTContext) -> bool {
        ctx.get_smt_solver_mut()
            .push()
            .expect("Failed to push SMT frame in preprocessor");

        let s_expr = (!expr.clone())
            .encode_to_smt_with_ctx(ctx.get_smt_solver(), ctx)
            .expect("Failed to encode rule guard in preprocessor");

        let res = ctx
            .assert_and_check_expr(s_expr)
            .expect("Failed to check SMT query in preprocessor");

        ctx.get_smt_solver_mut()
            .pop()
            .expect("Failed to pop SMT frame in preprocessor");

        !res.is_sat()
    }

    /// Check if a boolean expression is trivially true using an SMT solver and
    /// store the result in a cache
    fn is_trivially_true_with_cache(
        expr: &BooleanExpression<Variable>,
        ctx: &mut StaticSMTContext,
        cached_checks: &mut HashMap<BooleanExpression<Variable>, bool>,
    ) -> bool {
        if cached_checks.contains_key(expr) {
            return cached_checks[expr];
        }

        let res = Self::is_trivially_true(expr, ctx);
        cached_checks.insert(expr.clone(), res);
        res
    }

    /// Replace trivially true boolean expressions with `true`
    ///
    /// This function checks if the expression is trivially true using an SMT
    /// solver. If it is, the expression is replaced with `true`.
    ///
    /// This function also keeps track of known tautologies and guards to avoid
    /// repeated checks. These are stored in the `known_tautologies` and
    /// `known_guards` sets respectively.
    fn check_expr_and_replace_tautologies(
        expr: &mut BooleanExpression<Variable>,
        ctx: &mut StaticSMTContext,
        cached_checks: &mut HashMap<BooleanExpression<Variable>, bool>,
    ) {
        if expr == &BooleanExpression::True || expr == &BooleanExpression::False {
            return;
        }

        if Self::is_trivially_true_with_cache(expr, ctx, cached_checks) {
            trace!("Replaced guard \"{expr}\" with true");
            *expr = BooleanExpression::True;
            return;
        }

        // recursively check the subexpressions
        match expr {
            BooleanExpression::BinaryExpression(lhs, _, rhs) => {
                Self::check_expr_and_replace_tautologies(lhs.as_mut(), ctx, cached_checks);
                Self::check_expr_and_replace_tautologies(rhs.as_mut(), ctx, cached_checks);
            }
            BooleanExpression::Not(expr) => {
                Self::check_expr_and_replace_tautologies(expr.as_mut(), ctx, cached_checks)
            }
            BooleanExpression::ComparisonExpression(_, _, _)
            | BooleanExpression::True
            | BooleanExpression::False => (),
        }
    }
}

impl<S: TASpecification, C: ModelCheckerContext + ProvidesSMTSolverBuilder>
    Preprocessor<GeneralThresholdAutomaton, S, C> for ReplaceTrivialGuardsSMT
{
    fn process(&self, ta: &mut GeneralThresholdAutomaton, _spec: &S, ctx: &C) {
        let solver_builder = ctx.get_solver_builder().clone();

        let mut ctx = StaticSMTContext::new(
            solver_builder,
            ta.parameters().cloned(),
            Vec::new(),
            ta.variables().cloned(),
        )
        .expect("Failed to create SMT context for preprocessing");

        let rc = encode_resilience_condition(ta, ctx.get_smt_solver(), &ctx);
        ctx.get_smt_solver_mut()
            .assert(rc)
            .expect("Failed to assert resilience condition");

        ta.variables().for_each(|var| {
            let solver = ctx.get_smt_solver();
            let gt_0 = solver.gte(ctx.get_expr_for(var).unwrap(), solver.numeral(0));

            ctx.get_smt_solver_mut()
                .assert(gt_0)
                .expect("Failed to assert gt_0");
        });

        let mut cache = HashMap::new();

        ta.transform_rules(|rule| {
            rule.transform_guard(|expr| {
                Self::check_expr_and_replace_tautologies(expr, &mut ctx, &mut cache);
            });
        });

        if !cache.is_empty() {
            info!(
                "Preprocessor 'ReplaceTrivialGuardsSMT' on '{}' replaced {} trivial guards",
                ta.name(),
                cache.iter().filter(|(_, trivial)| **trivial).count(),
            );
        }
    }
}

/// Preprocessor that removes unused variables from the threshold automaton
pub struct RemoveUnusedVariables {}

impl Default for RemoveUnusedVariables {
    fn default() -> Self {
        Self::new()
    }
}

impl RemoveUnusedVariables {
    /// Create a new instance of the preprocessor
    pub fn new() -> Self {
        Self {}
    }

    fn get_unused_variables(ta: &GeneralThresholdAutomaton) -> impl Iterator<Item = &Variable> {
        ta.variables()
            .filter(|var| {
                !ta.rules()
                    .map(|r| r.guard())
                    .any(|g| g.contains_atom_a(var))
            })
            .filter(|var| {
                !ta.initial_variable_conditions().any(|ic| {
                    ic.contains_atom_a(var) && !ic.try_check_expr_constraints_to_zero(var)
                })
            })
    }

    fn remove_actions_using_variables(r: &mut Rule, vars: &[Variable]) {
        r.retain_actions(|a| !vars.contains(a.variable()));
    }
}
impl<S: TASpecification, C: ModelCheckerContext> Preprocessor<GeneralThresholdAutomaton, S, C>
    for RemoveUnusedVariables
{
    fn process(&self, ta: &mut GeneralThresholdAutomaton, _spec: &S, _ctx: &C) {
        let unused_variables = Self::get_unused_variables(ta).cloned().collect::<Vec<_>>();

        if unused_variables.is_empty() {
            return;
        }

        ta.transform_rules(|rule| {
            Self::remove_actions_using_variables(rule, &unused_variables);
        });

        unused_variables.iter().for_each(|var| {
            ta.remove_variable_and_replace_with(var, IntegerExpression::Const(0));
        });

        info!(
            "Preprocessor 'RemoveUnusedVariables' on '{}' removed {} unused variables",
            ta.name(),
            unused_variables.len(),
        );
    }
}

/// Preprocessor that checks whether the initial conditions of threshold
/// automaton are satisfiable at all.
/// If this is not the case, replaces them with false and deletes all rules
pub struct CheckInitCondSatSMT {}

impl Default for CheckInitCondSatSMT {
    fn default() -> Self {
        Self::new()
    }
}

impl CheckInitCondSatSMT {
    /// Create a new instance of the [CheckInitCondSatSMT] preprocessor
    pub fn new() -> Self {
        Self {}
    }
}

impl<S: TASpecification, C: ModelCheckerContext + ProvidesSMTSolverBuilder>
    Preprocessor<GeneralThresholdAutomaton, S, C> for CheckInitCondSatSMT
{
    fn process(&self, ta: &mut GeneralThresholdAutomaton, _spec: &S, ctx: &C) {
        let solver_builder = ctx.get_solver_builder();

        let mut ctx = StaticSMTContext::new(
            solver_builder,
            ta.parameters().cloned(),
            ta.locations().cloned(),
            ta.variables().cloned(),
        )
        .expect("Failed to create SMT context for preprocessing");

        let init_cond = encode_initial_constraints(ta, ctx.get_smt_solver(), &ctx);

        let init_cond_is_satisfiable = ctx
            .assert_and_check_expr(init_cond)
            .expect("Failed to encode initial conditions during preprocessing");

        if !init_cond_is_satisfiable.is_sat() {
            info!("Preprocessor 'CheckInitCondSatSMT' found unsatisfiable case.");
            ta.retain_rules(|_| false);
            ta.add_initial_location_constraints([BooleanExpression::False]);
            ta.add_initial_variable_constraints([BooleanExpression::False]);
        }
    }
}

/// Preprocessor that drops rules where the guards are unsatisfiable
///
/// This preprocessor encodes the resilience condition of the threshold
/// automaton into an SMT solver and checks whether rule guards are satisfiable.
///
/// If a rule guard is unsatisfiable, the rule is removed from the threshold
/// automaton.
///
/// This preprocessing step is useful for machine generated threshold automata
/// or if the resilience condition is complex. As it uses an SMT solver, it can
/// be very expensive.
pub struct DropUnsatisfiableRules {}

impl Default for DropUnsatisfiableRules {
    fn default() -> Self {
        Self::new()
    }
}

impl DropUnsatisfiableRules {
    /// Create a new instance of the preprocessor
    pub fn new() -> Self {
        Self {}
    }

    /// Check whether the guard of the rule is satisfiable
    fn get_unsatisfiable_rules<T: ThresholdAutomaton>(
        &self,
        solver_builder: SMTSolverBuilder,
        ta: &T,
    ) -> impl Iterator<Item = T::Rule> {
        let mut ctx = StaticSMTContext::new(
            solver_builder,
            ta.parameters().cloned(),
            Vec::new(),
            ta.variables().cloned(),
        )
        .expect("Failed to create SMT context for preprocessing");

        let rc = ta
            .resilience_conditions()
            .map(|rc| rc.encode_to_smt_with_ctx(ctx.get_smt_solver(), &ctx))
            .collect::<Result<Vec<_>, _>>()
            .expect("Failed to encode resilience condition");

        let rc = ctx.get_smt_solver().and_many(rc);

        ctx.get_smt_solver_mut()
            .assert(rc)
            .expect("Failed to assert resilience condition");

        ta.rules()
            .filter(move |rule| {
                // push new frame
                ctx.get_smt_solver_mut()
                    .push()
                    .expect("Failed to create new SMT frame");

                let guard = rule
                    .guard()
                    .as_boolean_expr()
                    .encode_to_smt_with_ctx(ctx.get_smt_solver(), &ctx)
                    .expect("Failed to encode guard");

                let res = ctx
                    .assert_and_check_expr(guard)
                    .expect("Failed to verify guard satisfiability SMT query");

                // pop the frame
                ctx.get_smt_solver_mut()
                    .pop()
                    .expect("Failed to pop SMT frame");

                !res.is_sat()
            })
            .cloned()
            .collect::<Vec<_>>()
            .into_iter()
    }
}

impl<
    T: ModifiableThresholdAutomaton,
    S: TASpecification,
    C: ModelCheckerContext + ProvidesSMTSolverBuilder,
> Preprocessor<T, S, C> for DropUnsatisfiableRules
{
    fn process(&self, ta: &mut T, _spec: &S, ctx: &C) {
        let n_rules = ta.rules().count();

        let solver_builder = ctx.get_solver_builder().clone();

        let unsat = self
            .get_unsatisfiable_rules(solver_builder, ta)
            .collect::<Vec<_>>();
        ta.retain_rules(|r| !unsat.contains(r));

        info!(
            "Preprocessor 'DropUnsatisfiableRules' on '{}' found and removed {} of {} unsatisfiable rules",
            ta.name(),
            n_rules - ta.rules().count(),
            n_rules
        );
    }
}

/// Preprocessor that collapses locations that have the same outgoing transitions and are not mentioned in the specification into one location
///
/// This preprocessor checks whether there exists locations that can be collapsed together and handles the collapsing in that case.
///
/// Locations are collapsable if they have the same outgoing transitions and are not mentioned in the specification.
pub struct CollapseLocations {}

impl Default for CollapseLocations {
    fn default() -> Self {
        Self::new()
    }
}

impl CollapseLocations {
    /// Create a new instance of the `CollapsableLocations` preprocessor
    pub fn new() -> Self {
        Self {}
    }

    /// Return all the different sets of collapsable locations
    fn compute_collapsable_locations<T: ThresholdAutomaton>(
        &self,
        ta: &T,
        locs_to_keep: &HashSet<&Location>,
    ) -> Vec<Vec<Location>>
    where
        <T as ThresholdAutomaton>::Rule: Eq + std::hash::Hash,
    {
        let mut collapsable_sets = Vec::new();
        let unreferenced_locations: HashSet<Location> = ta
            .locations()
            .filter(|loc| !locs_to_keep.contains(loc) && !ta.can_be_initial_location(loc))
            .cloned()
            .collect();
        for (i, loc1) in unreferenced_locations.iter().enumerate() {
            let mut current_set = Vec::new();
            current_set.push(loc1.clone());

            for loc2 in unreferenced_locations.iter().skip(i + 1) {
                if Self::have_same_outgoing_transitions(ta, loc1, loc2) {
                    current_set.push(loc2.clone());
                }
            }
            if current_set.len() > 1 {
                collapsable_sets.push(current_set);
            }
        }
        collapsable_sets
    }

    /// Return true if the two locations have the same outgoing transitions
    fn have_same_outgoing_transitions<T: ThresholdAutomaton>(
        ta: &T,
        loc1: &Location,
        loc2: &Location,
    ) -> bool
    where
        <T as ThresholdAutomaton>::Rule: Eq + std::hash::Hash,
    {
        let rules1 = ta
            .outgoing_rules(loc1)
            .filter(|x| x.source() != x.target())
            .map(|r| (r.target(), r.guard(), r.actions().collect::<BTreeSet<_>>()))
            .collect::<BTreeSet<_>>();

        let rules2 = ta
            .outgoing_rules(loc2)
            .map(|r| (r.target(), r.guard(), r.actions().collect::<BTreeSet<_>>()))
            .collect::<BTreeSet<_>>();

        rules1 == rules2
    }
}

impl<S: TASpecification, C: ModelCheckerContext> Preprocessor<GeneralThresholdAutomaton, S, C>
    for CollapseLocations
{
    fn process(&self, ta: &mut GeneralThresholdAutomaton, spec: &S, _ctx: &C) {
        let locations_to_keep: HashSet<&Location> = spec.locs_appearing().into_iter().collect();

        let n_locations = ta.locations().count();
        let n_rules = ta.rules().count();

        loop {
            let sets = self.compute_collapsable_locations(ta, &locations_to_keep);
            if sets.is_empty() {
                break;
            }

            for collapsable_set in sets {
                if let Some(first) = collapsable_set.first() {
                    let kept_location: Location = first.clone();
                    let collapsable_set = &collapsable_set[1..];

                    ta.retain_rules(|r| !collapsable_set.contains(r.source()));

                    ta.transform_rules(|rule| {
                        if collapsable_set.contains(rule.target()) {
                            rule.update_target(kept_location.clone());
                        }
                    });

                    for loc in collapsable_set {
                        ta.remove_location_and_replace_with(loc, IntegerExpression::Const(0));
                    }
                }
            }
        }

        info!(
            "Preprocessing removed {} locations, also removing {} rules.",
            n_locations - ta.locations().count(),
            n_rules - ta.rules().count(),
        );
    }
}

/// Enum representing all available preprocessors
///
/// This enum is used to configure what preprocessors can be used in TACO
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "config_deserialize", derive(Deserialize))]
pub enum ExistingPreprocessors {
    /// Removes self loops from the threshold automaton if the transition rule
    /// has no effect on the shared variables.
    DropSelfLoops,
    /// Removes unreachable locations from the threshold automaton by
    /// performing a graph search
    DropUnreachableLocations,
    /// Replaces some frequently generated guards that are always enabled with
    /// true
    ReplaceTrivialGuardsStatic,
    /// Replaces guards which are always satisfied, uses SMT to determine
    /// which guards are always satisfied.
    ReplaceTrivialGuardsSMT,
    /// Remove variables that do not appear in any guard
    RemoveUnusedVariables,
    /// Remove Rules for which a guard can never be satisfied
    DropUnsatisfiableRules,
    /// Collapse locations which have the same incoming rules
    CollapseLocations,
    /// Checks whether the initial location of the threshold automaton can be
    /// satisfied at all
    CheckInitCondSatSMT,
}

impl<S, C> From<ExistingPreprocessors> for Box<dyn Preprocessor<GeneralThresholdAutomaton, S, C>>
where
    S: TASpecification,
    C: ModelCheckerContext + ProvidesSMTSolverBuilder,
{
    fn from(val: ExistingPreprocessors) -> Self {
        match val {
            ExistingPreprocessors::DropSelfLoops => Box::new(DropSelfLoops::default()),
            ExistingPreprocessors::DropUnreachableLocations => {
                Box::new(DropUnreachableLocations::default())
            }
            ExistingPreprocessors::ReplaceTrivialGuardsStatic => {
                Box::new(ReplaceTrivialGuardsStatic::default())
            }
            ExistingPreprocessors::ReplaceTrivialGuardsSMT => {
                Box::new(ReplaceTrivialGuardsSMT::default())
            }
            ExistingPreprocessors::RemoveUnusedVariables => {
                Box::new(RemoveUnusedVariables::default())
            }
            ExistingPreprocessors::DropUnsatisfiableRules => {
                Box::new(DropUnsatisfiableRules::default())
            }
            ExistingPreprocessors::CollapseLocations => Box::new(CollapseLocations::default()),
            ExistingPreprocessors::CheckInitCondSatSMT => Box::new(CheckInitCondSatSMT::default()),
        }
    }
}

impl fmt::Display for ExistingPreprocessors {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExistingPreprocessors::DropSelfLoops => write!(f, "DropSelfLoops"),
            ExistingPreprocessors::DropUnreachableLocations => {
                write!(f, "DropUnreachableLocations")
            }
            ExistingPreprocessors::ReplaceTrivialGuardsStatic => {
                write!(f, "ReplaceTrivialGuardsStatic")
            }
            ExistingPreprocessors::ReplaceTrivialGuardsSMT => write!(f, "ReplaceTrivialGuardsSMT"),
            ExistingPreprocessors::RemoveUnusedVariables => write!(f, "RemoveUnusedVariables"),
            ExistingPreprocessors::DropUnsatisfiableRules => write!(f, "DropUnsatisfiableRules"),
            ExistingPreprocessors::CollapseLocations => write!(f, "CollapseLocations"),
            ExistingPreprocessors::CheckInitCondSatSMT => write!(f, "CheckInitCondSatSMT"),
        }
    }
}

#[cfg(test)]
mod test {

    use core::fmt;

    use taco_threshold_automaton::{
        BooleanVarConstraint,
        expressions::{
            BooleanExpression, ComparisonOp, IntegerExpression, Location, Parameter, Variable,
        },
        general_threshold_automaton::{
            Action,
            builder::{GeneralThresholdAutomatonBuilder, RuleBuilder},
        },
    };

    use crate::internal_spec::upwards_closed_set::UpwardsClosedSet;

    use super::*;

    pub struct DummySpec(HashSet<Location>);

    impl DummySpec {
        fn new() -> Self {
            Self(HashSet::new())
        }
    }

    impl TASpecification for DummySpec {
        fn locs_appearing(&self) -> impl IntoIterator<Item = &Location> {
            self.0.iter()
        }

        fn var_constraint(
            &self,
        ) -> impl IntoIterator<
            Item = &taco_threshold_automaton::lia_threshold_automaton::LIAVariableConstraint,
        > {
            unimplemented!();
            #[allow(unreachable_code)]
            Vec::new()
        }
    }

    impl fmt::Display for DummySpec {
        fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            unimplemented!()
        }
    }

    #[derive(Debug, Clone)]
    pub struct DummyContext;

    impl ModelCheckerContext for DummyContext {
        type CreationError = std::convert::Infallible;

        type ContextOptions = ();

        fn try_new(_opt: Option<Self::ContextOptions>) -> Result<Self, Self::CreationError> {
            unimplemented!()
        }
    }

    #[test]
    fn test_drop_self_loops() {
        let loc1 = Location::new("loc1");
        let loc2 = Location::new("loc2");
        let loc3 = Location::new("loc3");

        let var1 = Variable::new("var1");
        let var2 = Variable::new("var2");

        let r0 = RuleBuilder::new(0, loc1.clone(), loc1.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();
        let r1 = RuleBuilder::new(1, loc1.clone(), loc2.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();
        let r2 = RuleBuilder::new(2, loc1.clone(), loc1.clone())
            .with_guard(BooleanVarConstraint::True)
            .with_action(Action::new(var1.clone(), IntegerExpression::Atom(var1.clone())).unwrap())
            .build();
        let r3 = RuleBuilder::new(3, loc1.clone(), loc1.clone())
            .with_guard(BooleanVarConstraint::True)
            .with_action(
                Action::new(
                    var1.clone(),
                    IntegerExpression::Atom(var1.clone()) + IntegerExpression::Const(1),
                )
                .unwrap(),
            )
            .build();
        let r4 = RuleBuilder::new(4, loc2.clone(), loc2.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();
        let r5 = RuleBuilder::new(5, loc3.clone(), loc3.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();

        let mut ta = GeneralThresholdAutomatonBuilder::new("ta".to_string())
            .with_variables([var1, var2])
            .unwrap()
            .with_locations([loc1.clone(), loc2.clone(), loc3.clone()])
            .unwrap()
            .initialize()
            .with_rules([
                r0.clone(),
                r1.clone(),
                r2.clone(),
                r3.clone(),
                r4.clone(),
                r5.clone(),
            ])
            .unwrap()
            .build();

        DropSelfLoops::new().process(&mut ta, &DummySpec::new(), &DummyContext {});

        assert_eq!(ta.rules().count(), 2);
        assert!(!ta.rules().any(|r| r0 == *r));
        assert!(ta.rules().any(|r| r1 == *r));
        assert!(!ta.rules().any(|r| r2 == *r));
        assert!(ta.rules().any(|r| r3 == *r));
        assert!(!ta.rules().any(|r| r4 == *r));
        assert!(!ta.rules().any(|r| r5 == *r));
    }

    #[test]
    fn test_drop_unreachable_locations() {
        let loc1 = Location::new("loc1");
        let loc2 = Location::new("loc2");
        let loc3 = Location::new("loc3");
        let loc4 = Location::new("loc4");
        let loc5 = Location::new("loc5");

        let var1 = Variable::new("var1");
        let var2 = Variable::new("var2");

        let r0 = RuleBuilder::new(0, loc1.clone(), loc1.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();
        let r1 = RuleBuilder::new(1, loc1.clone(), loc2.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();
        let r2 = RuleBuilder::new(2, loc2.clone(), loc3.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();
        let r3 = RuleBuilder::new(3, loc4.clone(), loc5.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();

        let mut ta = GeneralThresholdAutomatonBuilder::new("ta".to_string())
            .with_variables([var1, var2])
            .unwrap()
            .with_locations([
                loc1.clone(),
                loc2.clone(),
                loc3.clone(),
                loc4.clone(),
                loc5.clone(),
            ])
            .unwrap()
            .initialize()
            .with_rules([r0.clone(), r1.clone(), r2.clone(), r3.clone()])
            .unwrap()
            .with_initial_location_constraints([
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc2.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc3.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc4.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ])
            .unwrap()
            .build();

        DropUnreachableLocations::new().process(&mut ta, &DummySpec::new(), &DummyContext {});

        assert_eq!(ta.locations().count(), 4);
        assert!(ta.locations().any(|l| *l == loc1));
        assert!(ta.locations().any(|l| *l == loc2));
        assert!(ta.locations().any(|l| *l == loc3));
        assert!(!ta.locations().any(|l| *l == loc4));
        assert!(ta.locations().any(|l| *l == loc5));

        assert_eq!(ta.rules().count(), 3);
        assert!(ta.rules().any(|r| r0 == *r));
        assert!(ta.rules().any(|r| r1 == *r));
        assert!(ta.rules().any(|r| r2 == *r));
        assert!(!ta.rules().any(|r| r3 == *r));
    }

    #[test]
    fn test_drop_unreachable_locations_and_modify_init_constraints() {
        let loc1 = Location::new("loc1");
        let loc2 = Location::new("loc2");
        let loc3 = Location::new("loc3");
        let loc4 = Location::new("loc4");
        let loc5 = Location::new("loc5");

        let var1 = Variable::new("var1");
        let var2 = Variable::new("var2");

        let r0 = RuleBuilder::new(0, loc1.clone(), loc1.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();
        let r1 = RuleBuilder::new(1, loc1.clone(), loc2.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();
        let r2 = RuleBuilder::new(2, loc2.clone(), loc3.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();
        let r3 = RuleBuilder::new(3, loc4.clone(), loc5.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();

        let mut ta = GeneralThresholdAutomatonBuilder::new("ta".to_string())
            .with_variables([var1, var2])
            .unwrap()
            .with_locations([
                loc1.clone(),
                loc2.clone(),
                loc3.clone(),
                loc4.clone(),
                loc5.clone(),
            ])
            .unwrap()
            .initialize()
            .with_rules([r0.clone(), r1.clone(), r2.clone(), r3.clone()])
            .unwrap()
            .with_initial_location_constraints([
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc2.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc3.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc4.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ])
            .unwrap()
            .build();

        DropUnreachableLocations::new().process(&mut ta, &DummySpec::new(), &DummyContext {});

        assert_eq!(ta.locations().count(), 4);
        assert!(ta.locations().any(|l| *l == loc1));
        assert!(ta.locations().any(|l| *l == loc2));
        assert!(ta.locations().any(|l| *l == loc3));
        assert!(!ta.locations().any(|l| *l == loc4));
        assert!(ta.locations().any(|l| *l == loc5));

        assert_eq!(ta.rules().count(), 3);
        assert!(ta.rules().any(|r| r0 == *r));
        assert!(ta.rules().any(|r| r1 == *r));
        assert!(ta.rules().any(|r| r2 == *r));
        assert!(!ta.rules().any(|r| r3 == *r));

        assert!(ta.initial_location_conditions().any(|l| l
            == &BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(loc2.clone())),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            )));
        assert!(ta.initial_location_conditions().any(|l| l
            == &BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(loc3.clone())),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            )));
        assert!(!ta.initial_location_conditions().any(|l| l
            == &BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(loc4.clone())),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            )));
    }

    #[test]
    fn test_combine_trivial_guards_static() {
        let loc1 = Location::new("loc1");
        let loc2 = Location::new("loc2");
        let loc3 = Location::new("loc3");
        let loc4 = Location::new("loc4");
        let loc5 = Location::new("loc5");

        let var1 = Variable::new("var1");
        let var2 = Variable::new("var2");

        let r0 = RuleBuilder::new(0, loc1.clone(), loc1.clone())
            .with_guard(BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Geq,
                Box::new(IntegerExpression::Const(0)),
            ))
            .build();
        let r1 = RuleBuilder::new(1, loc1.clone(), loc2.clone())
            .with_guard(BooleanVarConstraint::BinaryExpression(
                Box::new(BooleanVarConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                    ComparisonOp::Geq,
                    Box::new(IntegerExpression::Const(1)),
                )),
                BooleanConnective::Or,
                Box::new(BooleanVarConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )),
            ))
            .build();
        let r2 = RuleBuilder::new(2, loc2.clone(), loc3.clone())
            .with_guard(BooleanVarConstraint::BinaryExpression(
                Box::new(BooleanVarConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                    ComparisonOp::Neq,
                    Box::new(IntegerExpression::Const(5)),
                )),
                BooleanConnective::Or,
                Box::new(BooleanVarConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Const(6)),
                    ComparisonOp::Neq,
                    Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                )),
            ))
            .build();
        let r3 = RuleBuilder::new(3, loc4.clone(), loc5.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();

        let mut ta = GeneralThresholdAutomatonBuilder::new("ta".to_string())
            .with_variables([var1, var2])
            .unwrap()
            .with_locations([
                loc1.clone(),
                loc2.clone(),
                loc3.clone(),
                loc4.clone(),
                loc5.clone(),
            ])
            .unwrap()
            .initialize()
            .with_rules([r0.clone(), r1.clone(), r2.clone(), r3.clone()])
            .unwrap()
            .with_initial_location_constraints([
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc2.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc3.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc4.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ])
            .unwrap()
            .build();

        ReplaceTrivialGuardsStatic::new().process(
            &mut ta,
            &DummySpec::new(),
            &SMTSolverBuilder::default(),
        );

        assert_eq!(ta.rules().count(), 4);
        assert!(!ta.rules().any(|r| r0 == *r));
        assert!(!ta.rules().any(|r| r1 == *r));
        assert!(ta.rules().any(|r| r2 == *r));
        assert!(ta.rules().any(|r| r3 == *r));

        let r0 = RuleBuilder::new(0, loc1.clone(), loc1.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();
        let r1 = RuleBuilder::new(1, loc1.clone(), loc2.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();

        assert!(ta.rules().any(|r| r0 == *r));
        assert!(ta.rules().any(|r| r1 == *r));
    }

    #[test]
    fn test_combine_trivial_guards_smt() {
        let loc1 = Location::new("loc1");
        let loc2 = Location::new("loc2");
        let loc3 = Location::new("loc3");
        let loc4 = Location::new("loc4");
        let loc5 = Location::new("loc5");

        let var1 = Variable::new("var1");
        let var2 = Variable::new("var2");

        let r0 = RuleBuilder::new(0, loc1.clone(), loc1.clone())
            .with_guard(BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Geq,
                Box::new(IntegerExpression::Const(0)),
            ))
            .build();
        let r1 = RuleBuilder::new(1, loc1.clone(), loc2.clone())
            .with_guard(BooleanVarConstraint::BinaryExpression(
                Box::new(BooleanVarConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                    ComparisonOp::Geq,
                    Box::new(IntegerExpression::Const(5)),
                )),
                BooleanConnective::Or,
                Box::new(BooleanVarConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                    ComparisonOp::Lt,
                    Box::new(IntegerExpression::Const(5)),
                )),
            ))
            .build();
        let r2 = RuleBuilder::new(2, loc2.clone(), loc3.clone())
            .with_guard(
                BooleanVarConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                    ComparisonOp::Geq,
                    Box::new(IntegerExpression::Const(0)),
                ) & BooleanVarConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                    ComparisonOp::Lt,
                    Box::new(IntegerExpression::Const(42)),
                ),
            )
            .build();
        let r3 = RuleBuilder::new(3, loc4.clone(), loc5.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();

        let mut ta = GeneralThresholdAutomatonBuilder::new("ta".to_string())
            .with_variables([var1, var2])
            .unwrap()
            .with_locations([
                loc1.clone(),
                loc2.clone(),
                loc3.clone(),
                loc4.clone(),
                loc5.clone(),
            ])
            .unwrap()
            .with_parameter(Parameter::new("n"))
            .unwrap()
            .initialize()
            .with_resilience_condition(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Parameter::new("n"))),
                ComparisonOp::Geq,
                Box::new(IntegerExpression::Const(1)),
            ))
            .unwrap()
            .with_rules([r0.clone(), r1.clone(), r2.clone(), r3.clone()])
            .unwrap()
            .with_initial_location_constraints([
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc2.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc3.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc4.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ])
            .unwrap()
            .build();

        ReplaceTrivialGuardsSMT::new().process(
            &mut ta,
            &DummySpec::new(),
            &SMTSolverBuilder::default(),
        );

        assert_eq!(ta.rules().count(), 4);
        assert!(!ta.rules().any(|r| r0 == *r));
        assert!(!ta.rules().any(|r| r1 == *r));

        assert!(ta.rules().any(|r| r3 == *r));

        let r0 = RuleBuilder::new(0, loc1.clone(), loc1.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();
        let r1 = RuleBuilder::new(1, loc1.clone(), loc2.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();
        let r2 = RuleBuilder::new(2, loc2.clone(), loc3.clone())
            .with_guard(
                BooleanExpression::True
                    & BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                        ComparisonOp::Lt,
                        Box::new(IntegerExpression::Const(42)),
                    ),
            )
            .build();

        assert!(ta.rules().any(|r| r0 == *r));
        assert!(ta.rules().any(|r| r1 == *r));
        assert!(ta.rules().any(|r| r2 == *r));
    }

    #[test]
    fn test_remove_unused_variables() {
        let loc1 = Location::new("loc1");
        let loc2 = Location::new("loc2");
        let loc3 = Location::new("loc3");
        let loc4 = Location::new("loc4");
        let loc5 = Location::new("loc5");

        let var1 = Variable::new("var1");
        let var2 = Variable::new("var2");
        let var3 = Variable::new("var3");
        let var4 = Variable::new("var4");

        let r0 = RuleBuilder::new(0, loc1.clone(), loc1.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();
        let r1 = RuleBuilder::new(1, loc1.clone(), loc2.clone())
            .with_guard(BooleanVarConstraint::True)
            .with_action(Action::new_reset(var1.clone()))
            .build();
        let r2 = RuleBuilder::new(2, loc2.clone(), loc3.clone())
            .with_guard(BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(var3.clone())),
                ComparisonOp::Geq,
                Box::new(IntegerExpression::Const(0)),
            ))
            .build();
        let r3 = RuleBuilder::new(3, loc4.clone(), loc5.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();

        let mut ta = GeneralThresholdAutomatonBuilder::new("ta".to_string())
            .with_variables([var1.clone(), var2.clone(), var3.clone(), var4.clone()])
            .unwrap()
            .with_locations([
                loc1.clone(),
                loc2.clone(),
                loc3.clone(),
                loc4.clone(),
                loc5.clone(),
            ])
            .unwrap()
            .initialize()
            .with_rules([r0.clone(), r1.clone(), r2.clone(), r3.clone()])
            .unwrap()
            .with_initial_variable_constraints([
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(var1.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(var1.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(var4.clone())),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ])
            .unwrap()
            .build();

        RemoveUnusedVariables {}.process(&mut ta, &DummySpec::new(), &DummyContext {});

        assert_eq!(ta.variables().count(), 2);
        assert!(!ta.variables().any(|v| *v == var1));
        assert!(!ta.variables().any(|v| *v == var2));
        assert!(ta.variables().any(|v| *v == var3));
        assert!(ta.variables().any(|v| *v == var4));
    }

    #[test]
    fn test_init_cond_sat() {
        let loc1 = Location::new("loc1");
        let loc2 = Location::new("loc2");
        let loc3 = Location::new("loc3");
        let loc4 = Location::new("loc4");
        let loc5 = Location::new("loc5");

        let var1 = Variable::new("var1");
        let var2 = Variable::new("var2");

        let r0 = RuleBuilder::new(0, loc1.clone(), loc1.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();
        let r1 = RuleBuilder::new(1, loc1.clone(), loc2.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();
        let r2 = RuleBuilder::new(2, loc2.clone(), loc3.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();
        let r3 = RuleBuilder::new(3, loc4.clone(), loc5.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();

        let mut ta = GeneralThresholdAutomatonBuilder::new("ta".to_string())
            .with_variables([var1, var2])
            .unwrap()
            .with_locations([
                loc1.clone(),
                loc2.clone(),
                loc3.clone(),
                loc4.clone(),
                loc5.clone(),
            ])
            .unwrap()
            .initialize()
            .with_rules([r0.clone(), r1.clone(), r2.clone(), r3.clone()])
            .unwrap()
            .with_initial_location_constraints([
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc2.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc2.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(1)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc3.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc4.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ])
            .unwrap()
            .build();

        CheckInitCondSatSMT::default().process(
            &mut ta,
            &DummySpec::new(),
            &SMTSolverBuilder::default(),
        );

        assert_eq!(ta.rules().count(), 0);
        assert!(
            ta.initial_variable_conditions()
                .any(|c| c == &BooleanExpression::False)
        );
        assert!(
            ta.initial_location_conditions()
                .any(|c| c == &BooleanExpression::False)
        )
    }

    #[test]
    fn test_collapse_locations_no_spec() {
        let loc1 = Location::new("loc1");
        let loc2 = Location::new("loc2");
        let loc3 = Location::new("loc3");
        let loc4 = Location::new("loc4");
        let loc5 = Location::new("loc5");
        let loc6 = Location::new("loc6");
        let loc7 = Location::new("loc7");

        let var1 = Variable::new("var1");
        let var2 = Variable::new("var2");

        let r0 = RuleBuilder::new(0, loc1.clone(), loc2.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();
        let r1 = RuleBuilder::new(1, loc1.clone(), loc3.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();
        let r2 = RuleBuilder::new(2, loc1.clone(), loc4.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();
        let r3 = RuleBuilder::new(3, loc1.clone(), loc5.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();
        let r4 = RuleBuilder::new(4, loc2.clone(), loc6.clone())
            .with_guard(BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(var2.clone())),
                ComparisonOp::Geq,
                Box::new(IntegerExpression::Const(0)),
            ))
            .build();
        let r5 = RuleBuilder::new(5, loc3.clone(), loc6.clone())
            .with_guard(BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(var1.clone())),
                ComparisonOp::Geq,
                Box::new(IntegerExpression::Const(0)),
            ))
            .build();
        let r6 = RuleBuilder::new(6, loc4.clone(), loc6.clone())
            .with_guard(BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(var1.clone())),
                ComparisonOp::Geq,
                Box::new(IntegerExpression::Const(0)),
            ))
            .build();
        let r7 = RuleBuilder::new(7, loc5.clone(), loc7.clone())
            .with_guard(BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(var1.clone())),
                ComparisonOp::Geq,
                Box::new(IntegerExpression::Const(0)),
            ))
            .build();

        let mut ta = GeneralThresholdAutomatonBuilder::new("ta".to_string())
            .with_variables([var1.clone(), var2.clone()])
            .unwrap()
            .with_locations([
                loc1.clone(),
                loc2.clone(),
                loc3.clone(),
                loc4.clone(),
                loc5.clone(),
                loc6.clone(),
                loc7.clone(),
            ])
            .unwrap()
            .initialize()
            .with_rules([
                r0.clone(),
                r1.clone(),
                r2.clone(),
                r3.clone(),
                r4.clone(),
                r5.clone(),
                r6.clone(),
                r7.clone(),
            ])
            .unwrap()
            .with_initial_location_constraints([
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc2.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc3.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc4.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc5.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc6.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc7.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ])
            .unwrap()
            .build();

        CollapseLocations {}.process(&mut ta, &DummySpec::new(), &DummyContext {});

        assert_eq!(ta.locations().count(), 4);

        assert_eq!(ta.rules().count(), 6);
    }

    #[test]
    fn test_collapse_locations_with_spec() {
        let loc1 = Location::new("loc1");
        let loc2 = Location::new("loc2");
        let loc3 = Location::new("loc3");
        let loc4 = Location::new("loc4");

        let var1 = Variable::new("var1");

        let r0 = RuleBuilder::new(0, loc1.clone(), loc2.clone())
            .with_guard(BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(var1.clone())),
                ComparisonOp::Geq,
                Box::new(IntegerExpression::Const(0)),
            ))
            .build();
        let r1 = RuleBuilder::new(1, loc1.clone(), loc3.clone())
            .with_guard(BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(var1.clone())),
                ComparisonOp::Geq,
                Box::new(IntegerExpression::Const(0)),
            ))
            .build();
        let r2 = RuleBuilder::new(2, loc1.clone(), loc4.clone())
            .with_guard(BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(var1.clone())),
                ComparisonOp::Geq,
                Box::new(IntegerExpression::Const(0)),
            ))
            .build();

        let mut ta = GeneralThresholdAutomatonBuilder::new("ta".to_string())
            .with_variables([var1.clone()])
            .unwrap()
            .with_locations([loc1.clone(), loc2.clone(), loc3.clone(), loc4.clone()])
            .unwrap()
            .initialize()
            .with_rules([r0.clone(), r1.clone(), r2.clone()])
            .unwrap()
            .with_initial_location_constraints([
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc2.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc3.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc4.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ])
            .unwrap()
            .build();

        let spec = UpwardsClosedSet::new_cover([loc2.clone()]);

        CollapseLocations {}.process(&mut ta, &spec, &DummyContext {});

        assert_eq!(ta.locations().count(), 3);

        assert_eq!(ta.rules().count(), 3);
    }

    #[test]
    fn test_display_available_preprocessor() {
        assert_eq!(
            format!("{}", ExistingPreprocessors::DropSelfLoops),
            "DropSelfLoops"
        );
        assert_eq!(
            format!("{}", ExistingPreprocessors::DropUnreachableLocations),
            "DropUnreachableLocations"
        );
        assert_eq!(
            format!("{}", ExistingPreprocessors::ReplaceTrivialGuardsStatic),
            "ReplaceTrivialGuardsStatic"
        );
        assert_eq!(
            format!("{}", ExistingPreprocessors::ReplaceTrivialGuardsSMT),
            "ReplaceTrivialGuardsSMT"
        );
        assert_eq!(
            format!("{}", ExistingPreprocessors::RemoveUnusedVariables),
            "RemoveUnusedVariables"
        );
        assert_eq!(
            format!("{}", ExistingPreprocessors::DropUnsatisfiableRules),
            "DropUnsatisfiableRules"
        );
        assert_eq!(
            format!("{}", ExistingPreprocessors::CollapseLocations),
            "CollapseLocations"
        );
    }
}
