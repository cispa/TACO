//! This module contains the different symbolic model checkers (ZCS model checkers)
//! that operate on threshold automata and the 01-CS (ZCS).

mod paths;
pub mod smt_encoder_steady;
pub mod zcs;
pub mod zcs_error_graph;

use taco_interval_ta::IntervalThresholdAutomaton;

use log::{info, warn};

use taco_model_checker::ModelCheckerContext;
use taco_model_checker::internal_spec::ErrorSpec;
use taco_model_checker::internal_spec::ErrorTarget;
use taco_model_checker::internal_spec::upwards_closed_set::UpwardsClosedClause;
use taco_model_checker::internal_spec::upwards_closed_set::UpwardsClosedSet;
use taco_threshold_automaton::lia_threshold_automaton::LIAVariableConstraint;

use std::fmt::Display;
use taco_model_checker::{ModelChecker, ModelCheckerResult, SMTBddContext, TASpecOf};
use taco_threshold_automaton::ThresholdAutomaton;
use zcs::ZCS;
use zcs::ZCSStates;
use zcs::builder::ZCSBuilder;
use zcs_error_graph::ZCSErrorGraph;
use zcs_error_graph::builder::ZCSErrorGraphBuilder;

/// This struct defines a symbolic model checker (ZCS model checker)
/// It can be used to check reachability and coverability specifications
/// Depending on the chosen search heuristics:
/// - it can verify extended threshold automata with a semi-decision procedure
/// - it can verify canonical threshold automata with a decision procedure
#[derive(Debug, Clone)]
pub struct ZCSModelChecker {
    /// model checker context
    ctx: SMTBddContext,
    /// specifications to be checked
    ta_spec: TASpecOf<Self>,
    /// Properties that could not be translated
    unknown: Vec<String>,
    /// symbolic model checker heuristics
    heuristics: ZCSModelCheckerHeuristics,
}

impl ZCSModelChecker {
    /// constructs the symbolic 01-CS (ZCS) and initializes the bdd var manager
    fn compute_zcs<'a>(&'a self, ta: &'a IntervalThresholdAutomaton) -> ZCS<'a> {
        ZCSBuilder::new(self.ctx.bdd_manager(), ta).build()
    }

    /// construct the symbolic shared variable state that satisfies the interval
    /// constraint of a target configuration
    fn compute_enabled_shared_variable_states(
        cs: &ZCS,
        ta: &IntervalThresholdAutomaton,
        target_config: &UpwardsClosedClause,
    ) -> ZCSStates {
        let var_constr = target_config.variable_constr();
        let interval_constr = ta
            .get_interval_constraint(var_constr)
            .expect("Failed to get target interval_constr");

        ta.get_variables_constrained(&interval_constr)
            .into_iter()
            .map(|var| {
                // union over all intervals allowed for a variable
                ta.get_enabled_intervals(&interval_constr, var)
                    .map(|interval| cs.get_sym_state_for_shared_interval(var, interval))
                    .fold(cs.new_empty_sym_state(), |acc, x| acc.union(&x))
            })
            .fold(cs.new_full_sym_state(), |acc, x| acc.intersection(&x))
    }

    /// constructs the set of error states for a given spec and 01-CS (ZCS)
    fn compute_error_states(
        cs: &ZCS,
        ta: &IntervalThresholdAutomaton,
        specification: &UpwardsClosedSet,
    ) -> Result<ZCSStates, ZCSModelCheckerError> {
        let mut error_states = cs.new_empty_sym_state();

        for target_config in specification.upwards_closed_clauses() {
            let mut err_state = cs.new_full_sym_state();

            for (loc, _) in target_config.locs_to_cover() {
                err_state = err_state.intersection(&cs.get_sym_state_for_loc(loc));
            }

            for uncov in target_config.locs_to_uncover() {
                err_state = err_state.intersection(&cs.get_sym_state_for_loc(uncov).complement());
            }

            // Variable constraints
            if target_config.variable_constr() != &LIAVariableConstraint::True {
                let interval_err_state =
                    Self::compute_enabled_shared_variable_states(cs, ta, target_config);
                err_state = err_state.intersection(&interval_err_state);
            }

            error_states = error_states.union(&err_state);
        }

        Ok(error_states)
    }

    /// constructs the symbolic error graph (ZCS error graph) for the underlying 01-CS (ZCS)
    fn compute_symbolic_error_graph<'a>(
        &'a self,
        ta: &'a IntervalThresholdAutomaton,
        spec: &ErrorTarget,
    ) -> ZCSErrorGraph<'a> {
        let ErrorTarget::Reach(spec) = spec else {
            panic!("unsupported Liveness right now");
        };

        let cs = self.compute_zcs(ta);

        let error_states = Self::compute_error_states(&cs, ta, spec)
            .expect("The specification {} is not supported by the symbolic model checker");

        ZCSErrorGraphBuilder::new(cs.clone(), error_states).build()
    }
}

impl ModelChecker for ZCSModelChecker {
    type ModelCheckerContext = SMTBddContext;

    type ModelCheckerOptions = Option<ZCSModelCheckerHeuristics>;

    type SpecType = ErrorSpec;

    type ThresholdAutomatonType = IntervalThresholdAutomaton;

    type InitializationError = ZCSModelCheckerInitializationError;

    type ModelCheckingError = ZCSModelCheckerError;

    fn initialize(
        opts: Self::ModelCheckerOptions,
        ta_spec: TASpecOf<Self>,
        unknown: Vec<String>,
        ctx: Self::ModelCheckerContext,
    ) -> Result<Self, Self::InitializationError> {
        let heuristics;

        match opts.clone() {
            // No heuristics provided, use heuristics based on the given threshold automata
            None => {
                if ta_spec
                    .iter()
                    .any(|(_, _, tas)| tas.iter().any(|ta| ta.has_decrements_or_resets()))
                {
                    if ta_spec
                        .iter()
                        .any(|(_, _, tas)| tas.iter().any(|ta| ta.has_decrements()))
                    {
                        heuristics = ZCSModelCheckerHeuristics::DecrementAndIncrementHeuristics;
                    } else {
                        heuristics = ZCSModelCheckerHeuristics::ResetHeuristics;
                    }
                } else {
                    heuristics = ZCSModelCheckerHeuristics::CanonicalHeuristics;
                }
            }
            Some(h) => {
                heuristics = h;
            }
        }

        if opts == Some(ZCSModelCheckerHeuristics::CanonicalHeuristics)
            && ta_spec
                .iter()
                .any(|(_, _, tas)| tas.iter().any(|ta| ta.has_decrements_or_resets()))
        {
            return Err(ZCSModelCheckerInitializationError::HeuristicsNotSuitable(
                "Canonical heuristics".to_string(),
            ));
        }

        Ok(Self {
            ctx,
            ta_spec,
            unknown,
            heuristics,
        })
    }

    fn verify(
        self,
        abort_on_violation: bool,
    ) -> Result<ModelCheckerResult, Self::ModelCheckingError> {
        let mut unsafe_prop = Vec::new();
        let mut unknown_prop = self.unknown.clone();

        for (name, target, tas_to_check) in self.ta_spec.iter() {
            if !matches!(target, ErrorTarget::Reach(_)) {
                warn!("Property '{name}' ({target}) is not supported by the ZCS model checker");
                unknown_prop.push(name.clone());
                continue;
            }

            info!(
                "Starting to check property '{}', which requires {} model checker run(s).",
                name,
                tas_to_check.len()
            );
            for ta in tas_to_check.iter() {
                let error_graph = self.compute_symbolic_error_graph(ta, target);
                if !error_graph.is_empty() {
                    if self.heuristics == ZCSModelCheckerHeuristics::EmptyErrorGraphHeuristics {
                        info!(
                            "The error graph is not empty, but the chosen heuristics only checks for emptiness. Therefore, it is unknown whether the property holds."
                        );
                        unknown_prop.push(name.clone());
                        continue;
                    }
                    info!("The error graph is not empty, checking for non-spurious error paths.");
                    let res =
                        error_graph.contains_non_spurious_error_path(&ZCSModelCheckerContext::new(
                            &self.ctx,
                            self.heuristics.clone(),
                            ta,
                            target,
                        ));

                    if let Some(p) = res.non_spurious_path() {
                        info!("Property {} is not satisfied!", name);

                        unsafe_prop.push((name.clone(), Box::new(p.clone())));

                        if abort_on_violation {
                            return Ok(ModelCheckerResult::UNSAFE {
                                violations: unsafe_prop,
                                unknown: unknown_prop,
                            });
                        }

                        break;
                    }

                    info!("All error paths are spurious.");
                } else {
                    info!("The error graph is empty.");
                }
            }
        }

        if !unsafe_prop.is_empty() {
            return Ok(ModelCheckerResult::UNSAFE {
                violations: unsafe_prop,
                unknown: unknown_prop,
            });
        }
        if !unknown_prop.is_empty() {
            return Ok(ModelCheckerResult::UNKNOWN(unknown_prop));
        }

        Ok(ModelCheckerResult::SAFE)
    }
}

impl Default for ZCSModelChecker {
    fn default() -> Self {
        Self::new_mc(SMTBddContext::try_new(None).expect("Failed to create SMTBddContext"))
    }
}

impl ZCSModelChecker {
    /// new symbolic model checker with default settings
    pub fn new_mc(ctx: SMTBddContext) -> Self {
        Self {
            ctx,
            ta_spec: Vec::new(),
            unknown: Vec::new(),
            heuristics: ZCSModelCheckerHeuristics::CanonicalHeuristics,
        }
    }
}

/// Custom Error type to indicate an error
/// when running a symbolic model checker (ZCS model checker)
#[derive(Debug)]
pub enum ZCSModelCheckerError {
    /// Error indicating that the current specification is not supported by the current symbolic model checker
    SpecNotSupported(String),
}

impl std::error::Error for ZCSModelCheckerError {}

impl Display for ZCSModelCheckerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ZCSModelCheckerError::SpecNotSupported(spec) => write!(
                f,
                "This initialized symbolic model checker does not support the specification {spec}"
            ),
        }
    }
}

/// Custom Error type to indicate an error
/// when initializing a symbolic model checker (ZCS model checker)
#[derive(Debug)]
pub enum ZCSModelCheckerInitializationError {
    /// Error indicating that the current heuristics does not support the given TA
    HeuristicsNotSuitable(String),
}

impl std::error::Error for ZCSModelCheckerInitializationError {}

impl Display for ZCSModelCheckerInitializationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ZCSModelCheckerInitializationError::HeuristicsNotSuitable(heur) => write!(
                f,
                "The chosen heuristics {heur} is not suitable for the given threshold automaton",
            ),
        }
    }
}

/// This struct contains all the necessary configurations when using the symbolic model checker (ZCS model checker)
pub struct ZCSModelCheckerContext<'a> {
    /// used smt and bdd libraries
    ctx: &'a SMTBddContext,
    /// underlying heuristics
    heuristics: ZCSModelCheckerHeuristics,
    /// underlying TA
    ta: &'a IntervalThresholdAutomaton,
    /// underlying specification
    spec: &'a ErrorTarget,
    /// indicates if the symbolic model checker should print spurious counterexamples
    print_spurious_ce: bool,
}
impl<'a> ZCSModelCheckerContext<'a> {
    /// creates a new symbolic model checker context
    fn new(
        ctx: &'a SMTBddContext,
        heuristics: ZCSModelCheckerHeuristics,
        ta: &'a IntervalThresholdAutomaton,
        spec: &'a ErrorTarget,
    ) -> Self {
        ZCSModelCheckerContext {
            ctx,
            heuristics,
            ta,
            spec,
            print_spurious_ce: false,
        }
    }
    /// returns the SMTBddContext
    fn smt_bdd_context(&self) -> &SMTBddContext {
        self.ctx
    }
    /// returns the heuristics
    fn heuristics(&self) -> ZCSModelCheckerHeuristics {
        self.heuristics.clone()
    }
    /// returns the underlying TA
    fn ta(&self) -> &IntervalThresholdAutomaton {
        self.ta
    }
    /// returns the underlying specification
    fn spec(&self) -> &ErrorTarget {
        self.spec
    }
    /// returns if spurious counterexamples should be printed
    fn print_spurious_ce(&self) -> bool {
        self.print_spurious_ce
    }
}

/// this enum defines SymbolicModelChecker Heuristics,
/// such a heuristics defines which symbolic paths are ignored
/// and which specifications and threshold automata can be checked
///
/// Additionally it describes a greedy heuristics which only checks if the symbolic error graph is empty.
#[derive(PartialEq, Clone, Debug)]
pub enum ZCSModelCheckerHeuristics {
    /// this heuristics yields a semi-decision procedure
    /// by unfolding cycles if the given `ta` contains resets
    /// it can be used to verify extended threshold automata
    /// for coverability or reachability specifications
    ResetHeuristics,
    /// this heuristics yields a semi-decision procedure
    /// by unfolding cycles if the given `ta` contains increments and decrements
    /// it can be used to verify extended threshold automata
    /// for coverability or reachability specifications
    DecrementAndIncrementHeuristics,
    /// this heuristics yields a decision procedure
    /// by only traversing cycles once
    /// it can be used to verify canonical threshold automata (no resets/decrements)
    /// for coverability or reachability specifications
    CanonicalHeuristics,
    /// this is a greedy heuristics that only checks if the symbolic error graph is empty
    /// it is neither complete nor sound but guarantees termination
    /// if the error graph is empty the property holds, otherwise no conclusion can be drawn
    EmptyErrorGraphHeuristics,
}
impl ZCSModelCheckerHeuristics {
    /// returns a new ResetHeuristics
    pub fn new_reset_heuristics() -> Self {
        ZCSModelCheckerHeuristics::ResetHeuristics
    }
    /// returns a new DecrementsAndIncrementHeuristics
    pub fn new_decrement_and_increment_heuristics() -> Self {
        ZCSModelCheckerHeuristics::DecrementAndIncrementHeuristics
    }
    /// returns a new CanonicalHeuristics
    pub fn new_canonical_heuristics() -> Self {
        ZCSModelCheckerHeuristics::CanonicalHeuristics
    }
    /// returns a new CanonicalHeuristics
    pub fn new_empty_error_graph_heuristics() -> Self {
        ZCSModelCheckerHeuristics::EmptyErrorGraphHeuristics
    }
    /// returns true iff the heuristics ensures that every steady path is monotonic
    pub fn is_monotonic(&self) -> bool {
        match self {
            ZCSModelCheckerHeuristics::ResetHeuristics => true,
            ZCSModelCheckerHeuristics::DecrementAndIncrementHeuristics => false,
            ZCSModelCheckerHeuristics::CanonicalHeuristics => true,
            ZCSModelCheckerHeuristics::EmptyErrorGraphHeuristics => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ZCSModelChecker;
    use crate::ZCSModelCheckerHeuristics;
    use std::collections::HashMap;

    use taco_bdd::BDDManagerConfig;
    use taco_interval_ta::IntervalThresholdAutomaton;
    use taco_interval_ta::builder::IntervalTABuilder;
    use taco_interval_ta::interval::Interval;
    use taco_model_checker::ModelChecker;
    use taco_model_checker::ModelCheckerContext;
    use taco_model_checker::ModelCheckerResult;
    use taco_model_checker::SMTBddContext;

    use taco_model_checker::internal_spec::ErrorTarget;
    use taco_model_checker::internal_spec::upwards_closed_set::UpwardsClosedSet;
    use taco_parser::ParseTAWithLTL;
    use taco_parser::bymc::ByMCParser;
    use taco_smt_encoder::SMTSolverBuilder;
    use taco_smt_encoder::SMTSolverBuilderCfg;

    use taco_threshold_automaton::expressions::BooleanExpression;
    use taco_threshold_automaton::expressions::ComparisonOp;
    use taco_threshold_automaton::expressions::IntegerExpression;
    use taco_threshold_automaton::expressions::fraction::Fraction;
    use taco_threshold_automaton::expressions::{Location, Parameter, Variable};
    use taco_threshold_automaton::general_threshold_automaton::Action;
    use taco_threshold_automaton::general_threshold_automaton::UpdateExpression;
    use taco_threshold_automaton::general_threshold_automaton::builder::RuleBuilder;

    use taco_threshold_automaton::BooleanVarConstraint;
    use taco_threshold_automaton::LocationConstraint;
    use taco_threshold_automaton::ParameterConstraint;
    use taco_threshold_automaton::path::Configuration;
    use taco_threshold_automaton::path::PathBuilder;
    use taco_threshold_automaton::path::Transition;

    impl ZCSModelChecker {
        /// Create a new symbolic model checker (ZCS model checker)
        fn new_test(ctx: SMTBddContext) -> Self {
            ZCSModelChecker {
                ctx,
                ta_spec: Vec::new(),
                unknown: Vec::new(),
                heuristics: ZCSModelCheckerHeuristics::CanonicalHeuristics,
            }
        }
    }

    /// Construct the SymbolicErrorGraph for the following threshold automaton:
    ///
    /// Threshold Automaton:
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
    fn get_test_ata() -> IntervalThresholdAutomaton {
        let ta_builder =
            taco_threshold_automaton::general_threshold_automaton::builder::GeneralThresholdAutomatonBuilder::new("test")
                .with_locations(vec![
                    Location::new("l0"),
                    Location::new("l1"),
                    Location::new("l2"),
                ])
                .unwrap()
                .with_variables(vec![Variable::new("x")])
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
                        ComparisonOp::Geq,
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
                    )
                ]).unwrap()
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

    #[test]
    fn test_compute_symbolic_01_cs_no_bdd_mgr() {
        let ctx = SMTBddContext::try_new(None).unwrap();

        let smc = ZCSModelChecker::new_test(ctx);

        let ata = get_test_ata();
        let cs = smc.compute_zcs(&ata);

        let initial_states = cs.initial_states();

        let l_1 = cs.get_sym_state_for_loc(&Location::new("l1"));
        let l_2 = cs.get_sym_state_for_loc(&Location::new("l2"));

        // I_0 = [0,1)
        let interval_0 =
            Interval::new_constant(Fraction::new(0, 1, false), Fraction::new(1, 1, false));
        let x_i_0 = cs.get_sym_state_for_shared_interval(&Variable::new("x"), &interval_0.clone());

        let correct_initial_states = l_1
            .complement()
            .intersection(&l_2.complement())
            .intersection(&x_i_0);

        assert!(initial_states.equal(&correct_initial_states));
    }

    #[test]
    fn test_compute_symbolic_01_cs_some_bdd_mgr() {
        let ctx = SMTBddContext::try_new(None).unwrap();

        let smc = ZCSModelChecker::new_test(ctx);

        let ata = get_test_ata();
        let cs = smc.compute_zcs(&ata);

        let initial_states = cs.initial_states();

        let l_1 = cs.get_sym_state_for_loc(&Location::new("l1"));
        let l_2 = cs.get_sym_state_for_loc(&Location::new("l2"));

        // I_0 = [0,1)
        let interval_0 =
            Interval::new_constant(Fraction::new(0, 1, false), Fraction::new(1, 1, false));
        let x_i_0 = cs.get_sym_state_for_shared_interval(&Variable::new("x"), &interval_0.clone());

        let correct_initial_states = l_1
            .complement()
            .intersection(&l_2.complement())
            .intersection(&x_i_0);

        assert!(initial_states.equal(&correct_initial_states));
    }

    #[test]
    fn test_compute_error_states_cover() {
        let ctx = SMTBddContext::try_new(None).unwrap();

        let smc = ZCSModelChecker::new_test(ctx);

        let spec = UpwardsClosedSet::new_cover([Location::new("l2")]);

        let ata = get_test_ata();
        let cs = smc.compute_zcs(&ata);

        let error_states = ZCSModelChecker::compute_error_states(&cs, &ata, &spec);

        let l_2 = cs.get_sym_state_for_loc(&Location::new("l2"));

        assert!(error_states.is_ok());
        assert!(error_states.unwrap().equal(&l_2));
    }

    #[test]
    fn test_compute_error_states_reachability() {
        let ctx = SMTBddContext::try_new(None).unwrap();

        let smc = ZCSModelChecker::new_test(ctx);

        let spec = UpwardsClosedSet::new_reach([(Location::new("l2"), 1)], [Location::new("l1")]);

        let ata = get_test_ata();
        let cs = smc.compute_zcs(&ata);

        let error_states = ZCSModelChecker::compute_error_states(&cs, &ata, &spec);

        let l_1 = cs.get_sym_state_for_loc(&Location::new("l1"));
        let l_2 = cs.get_sym_state_for_loc(&Location::new("l2"));

        assert!(error_states.is_ok());
        assert!(
            error_states
                .unwrap()
                .equal(&l_2.intersection(&l_1.complement()))
        );
    }

    #[test]
    fn test_compute_error_states_general_cover() {
        let ctx = SMTBddContext::try_new(None).unwrap();

        let smc = ZCSModelChecker::new_test(ctx);

        let spec = UpwardsClosedSet::new_cover_int([(Location::new("l2"), 2)]);

        let ata = get_test_ata();
        let cs = smc.compute_zcs(&ata);

        let error_states = ZCSModelChecker::compute_error_states(&cs, &ata, &spec);

        let l_2 = cs.get_sym_state_for_loc(&Location::new("l2"));

        assert!(error_states.is_ok());
        assert!(error_states.unwrap().equal(&l_2));
    }

    #[test]
    fn test_compute_enabled_shared_variable_states() {
        let ctx = SMTBddContext::try_new(None).unwrap();

        let smc = ZCSModelChecker::new_test(ctx);

        let spec = UpwardsClosedSet::new_var_constraint(
            BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("x"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            )
            .try_into()
            .unwrap(),
        ) & UpwardsClosedSet::new_cover_int([(Location::new("l2"), 2)]);
        let spec = spec.upwards_closed_clauses().next().unwrap();

        let ata = get_test_ata();
        let cs = smc.compute_zcs(&ata);

        let error_interval_state =
            ZCSModelChecker::compute_enabled_shared_variable_states(&cs, &ata, spec);

        let i_1 = cs
            .get_sym_state_for_shared_interval(&Variable::new("x"), &Interval::new_constant(0, 1));

        assert!(error_interval_state.equal(&i_1));
    }

    #[test]
    fn test_compute_error_states_reach_with_var_constr() {
        let ctx = SMTBddContext::try_new(None).unwrap();

        let smc = ZCSModelChecker::new_test(ctx);

        let spec = UpwardsClosedSet::new_cover_int([(Location::new("l2"), 2)])
            & UpwardsClosedSet::new_var_constraint(
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("x"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )
                .try_into()
                .unwrap(),
            );

        let ata = get_test_ata();
        let cs = smc.compute_zcs(&ata);

        let error_states = ZCSModelChecker::compute_error_states(&cs, &ata, &spec);

        let l_2 = cs.get_sym_state_for_loc(&Location::new("l2"));
        let i_1 = cs
            .get_sym_state_for_shared_interval(&Variable::new("x"), &Interval::new_constant(0, 1));
        let expected_err_state = l_2.intersection(&i_1);

        assert!(error_states.is_ok());
        assert!(error_states.unwrap().equal(&expected_err_state));
    }

    #[test]
    fn test_compute_error_states_all_spec_types() {
        let ctx = SMTBddContext::try_new(None).unwrap();

        let smc = ZCSModelChecker::new_test(ctx);

        let cover = UpwardsClosedSet::new_cover([Location::new("l2")]);

        let general_cover = UpwardsClosedSet::new_cover_int([(Location::new("l2"), 2)]);

        let reach = UpwardsClosedSet::new_reach([(Location::new("l2"), 2)], []);

        let spec = cover | general_cover | reach;

        let ata = get_test_ata();
        let cs = smc.compute_zcs(&ata);

        let error_states = ZCSModelChecker::compute_error_states(&cs, &ata, &spec);

        let l_2 = cs.get_sym_state_for_loc(&Location::new("l2"));

        assert!(error_states.is_ok());
        assert!(error_states.unwrap().equal(&l_2));
    }

    #[test]
    fn test_compute_symbolic_error_graph() {
        let ctx = SMTBddContext::try_new(None).unwrap();

        let smc = ZCSModelChecker::new_test(ctx);

        let ata = get_test_ata();

        let spec = UpwardsClosedSet::new_reach(
            [(Location::new("l2"), 1)],
            [Location::new("l0"), Location::new("l1")],
        );

        let sym_err_graph = smc.compute_symbolic_error_graph(&ata, &ErrorTarget::Reach(spec));

        assert!(!sym_err_graph.is_empty());
    }

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

        let mc = ZCSModelChecker::new(
            Some((
                Some(SMTSolverBuilderCfg::new_z3()),
                Some(BDDManagerConfig::new_cudd()),
            )),
            Some(ZCSModelCheckerHeuristics::CanonicalHeuristics),
            Vec::new(),
            ta.clone(),
            spec.into_iter(),
        );
        let mc = mc.unwrap();
        let res = mc.verify(true).unwrap();

        // Replicate interval ta for path builder
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

        let mc = ZCSModelChecker::new(
            Some((
                Some(SMTSolverBuilderCfg::new_z3()),
                Some(BDDManagerConfig::new_cudd()),
            )),
            Some(ZCSModelCheckerHeuristics::CanonicalHeuristics),
            Vec::new(),
            ta.clone(),
            spec.into_iter(),
        );
        let mc = mc.unwrap();
        let res = mc.verify(true).unwrap();

        // Replicate interval ta for path builder

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

            let mc = ZCSModelChecker::new(
                Some((
                    Some(SMTSolverBuilderCfg::new_z3()),
                    Some(BDDManagerConfig::new_cudd()),
                )),
                Some(ZCSModelCheckerHeuristics::CanonicalHeuristics),
                Vec::new(),
                ta,
                spec.expressions().iter().cloned(),
            );
            mc.expect("Failed to create model checker")
                .verify(false)
                .expect("Failed to model check")
        };

        // Violated in the initial configuration, i.e., by a path without
        // any transition
        let res = run("init_reach: [](loc1 == 0);");
        let ModelCheckerResult::UNSAFE { violations, .. } = res else {
            panic!("Expected UNSAFE, got {res:?}");
        };
        assert_eq!(violations.len(), 1);
        assert_eq!(violations[0].0, "init_reach");
        assert_eq!(violations[0].1.transitions().count(), 0);

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
