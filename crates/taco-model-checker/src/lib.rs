//! This module contains the different model checkers that are available in
//! TACO.
//! Every model checker needs to implement the [`ModelChecker`] trait.

use core::fmt;
use std::{convert::Infallible, error, fmt::Display};

use eltl::ELTLExpression;
use log::trace;
use taco_bdd::{BDDManager, BDDManagerConfig};
use taco_smt_encoder::{
    ProvidesSMTSolverBuilder, SMTSolverBuilder, SMTSolverBuilderCfg, SMTSolverBuilderError,
};
use taco_threshold_automaton::{
    ModifiableThresholdAutomaton, ThresholdAutomaton,
    expressions::Location,
    general_threshold_automaton::GeneralThresholdAutomaton,
    lia_threshold_automaton::{
        LIAThresholdAutomaton, LIATransformationError, LIAVariableConstraint,
    },
    path::Path,
};

use crate::preprocessing::Preprocessor;

pub mod eltl;
pub mod internal_spec;
pub mod preprocessing;

/// The context type used by the model checker `M`
pub type ContextOf<M> = <M as ModelChecker>::ModelCheckerContext;

/// The internal specification type the model checker `M` works on
pub type InternalSpecOf<M> =
    <<M as ModelChecker>::SpecType as SpecificationTrait<ContextOf<M>>>::InternalSpecType;

/// Error that can occur while transforming a general threshold automaton into
/// the internal representation of the model checker `M`
pub type TAErrorOf<M> = <<M as ModelChecker>::ThresholdAutomatonType as TATrait<
    ContextOf<M>,
    InternalSpecOf<M>,
>>::TransformationError;

/// Error that can occur while transforming an ELTL specification into the
/// internal specification of the model checker `M`
pub type SpecErrorOf<M> =
    <<M as ModelChecker>::SpecType as SpecificationTrait<ContextOf<M>>>::TransformationError;

/// Error that can occur while creating the context of the model checker `M`
pub type ContextErrorOf<M> = <ContextOf<M> as ModelCheckerContext>::CreationError;

/// Options accepted by the context of the model checker `M`
pub type ContextOptionsOf<M> = <ContextOf<M> as ModelCheckerContext>::ContextOptions;

/// Preprocessor that can be applied before the threshold automaton is
/// transformed into the internal representation of the model checker `M`
pub type PreprocessorOf<M> =
    Box<dyn Preprocessor<GeneralThresholdAutomaton, InternalSpecOf<M>, ContextOf<M>>>;

/// A specification paired with all threshold automata that need to be checked
/// to verify it, and the name of the property it was derived from
pub type TASpecOf<M> = Vec<(
    String,
    InternalSpecOf<M>,
    Vec<<M as ModelChecker>::ThresholdAutomatonType>,
)>;

/// The [`ModelChecker`] trait defines the interface for all model checkers in
/// TACO.
pub trait ModelChecker: Sized {
    /// Context for the model checker which for example includes interfaces to
    /// create solvers or BDD libraries
    type ModelCheckerContext: ModelCheckerContext;

    /// Options for the model checker
    type ModelCheckerOptions;

    /// Internal specification representation the model checker uses
    type SpecType: SpecificationTrait<Self::ModelCheckerContext>;
    /// Internal representation of a threshold automaton the model checker works
    /// on
    type ThresholdAutomatonType: TATrait<ContextOf<Self>, InternalSpecOf<Self>>;

    /// Error type for errors that can occur during initialization of the model
    /// checker
    type InitializationError: error::Error;
    /// Error type for errors that can occur during the run of the model checker
    type ModelCheckingError: error::Error;

    /// Initialize the model checker with the internal threshold automaton and
    /// specification representation
    ///
    /// This function needs to be implemented by all model checkers and should
    /// setup the model checker with the appropriate options, system and
    /// specification representation, as well as the context containing backend
    /// functionality like SMT solver configurations.
    ///
    /// `unknown` contains the names of properties that could not be
    /// translated into the internal specification. They must be reported as
    /// unknown by the model checker.
    fn initialize(
        opts: Self::ModelCheckerOptions,
        ta_spec: TASpecOf<Self>,
        unknown: Vec<String>,
        ctx: Self::ModelCheckerContext,
    ) -> Result<Self, Self::InitializationError>;

    /// Construct a new instance of the model checker
    ///
    /// This function will first try to construct the model checker context,
    /// then try to transform the threshold automaton into the internal type of
    /// the model checker, after which it will attempt to convert the
    /// specification into the internal type of the model checker.
    ///
    /// If any of these steps fail, or are not possible a
    /// `ModelCheckerSetupError` will be returned that contains the error of the
    /// stage it occurred.
    ///
    /// If the function returns an `Ok`, the model checker has been initialized
    /// with the threshold automaton and specification and is ready to be
    /// checked.
    fn new(
        ctx_opts: Option<ContextOptionsOf<Self>>,
        mc_opts: Self::ModelCheckerOptions,
        preprocessors: Vec<PreprocessorOf<Self>>,
        ta: GeneralThresholdAutomaton,
        spec: impl Iterator<Item = (String, ELTLExpression)>,
    ) -> Result<Self, ModelCheckerSetupError<Self>> {
        let ctx = Self::ModelCheckerContext::try_new(ctx_opts);
        if let Err(ctx_err) = ctx {
            return Err(ModelCheckerSetupError::ErrorContextSetup(ctx_err));
        }
        let ctx = ctx.unwrap();

        let spec = Self::SpecType::try_from_eltl(spec, &ctx);
        if let Err(spec_err) = spec {
            return Err(ModelCheckerSetupError::ErrorTransformingSpec(spec_err));
        }
        let (spec, unknown) = spec.unwrap();

        // Combine the specification with the threshold automaton
        let ta_spec = Self::SpecType::transform_threshold_automaton(ta, spec, &ctx);

        let ta_spec = ta_spec
            .into_iter()
            .map(|(name, spec, mut ta)| {
                // Preprocessing on tas with information from the specification
                for processor in preprocessors.iter() {
                    processor.process(&mut ta, &spec, &ctx);
                }

                trace!("Threshold automaton for property {spec} after preprocessing: {ta}");

                let ta = Self::ThresholdAutomatonType::try_from_general_ta(ta, &ctx, &spec)?;

                Ok((name, spec, ta))
            })
            .collect::<Result<Vec<_>, _>>();
        if let Err(ta_err) = ta_spec {
            return Err(ModelCheckerSetupError::ErrorTransformingTA(ta_err));
        }
        let ta_spec = ta_spec.unwrap();

        let mc = Self::initialize(mc_opts, ta_spec, unknown, ctx.clone());
        if let Err(mc_err) = mc {
            return Err(ModelCheckerSetupError::ErrorInitializingModelChecker(
                mc_err,
            ));
        }

        Ok(mc.unwrap())
    }

    /// Start the model checker
    ///
    /// This function starts the actual model checking process. The flag
    /// `abort_on_violation` specifies whether a model checker should continue
    /// after finding the first violation or continue
    fn verify(
        self,
        abort_on_violation: bool,
    ) -> Result<ModelCheckerResult, Self::ModelCheckingError>;
}

/// Result type for initialization of a model checker
///
/// The error is parameterized by the model checker it originates from, as every
/// stage of the setup reports the error type of that model checker.
#[derive(Debug)]
pub enum ModelCheckerSetupError<M: ModelChecker> {
    /// Could not initialize model checker because transformation of threshold
    /// automaton failed
    ErrorTransformingTA(TAErrorOf<M>),
    /// Could not initialize model checker because transformation of
    /// specification failed
    ErrorTransformingSpec(SpecErrorOf<M>),
    /// Could not initialize model checker because context could not be initialized
    ErrorContextSetup(ContextErrorOf<M>),
    /// Error that can occur during initialization
    ErrorInitializingModelChecker(M::InitializationError),
}

impl<M: ModelChecker> fmt::Display for ModelCheckerSetupError<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ModelCheckerSetupError::ErrorTransformingTA(e) => write!(
                f,
                "Failed to transform threshold automaton into required form for the model checker. Error: {e}"
            ),
            ModelCheckerSetupError::ErrorTransformingSpec(e) => write!(
                f,
                "Failed to transform specification into the required form for model checking. Error: {e}"
            ),
            ModelCheckerSetupError::ErrorContextSetup(e) => {
                write!(f, "Failed to setup model checking context. Error: {e}")
            }
            ModelCheckerSetupError::ErrorInitializingModelChecker(e) => {
                write!(f, "Failed to initialize the model checker. Error: {e}")
            }
        }
    }
}

/// Result type for a model checking run
#[derive(Debug, Clone, PartialEq)]
pub enum ModelCheckerResult {
    /// Threshold automaton fulfills all the specification
    SAFE,
    /// Threshold automaton does not fulfill the specification
    UNSAFE {
        /// Names of the violated specifications, each with a concrete error
        /// path that serves as an example for the violation
        violations: Vec<(String, Box<Path>)>,
        /// Names of the specifications for which the model checker could not
        /// determine whether they hold
        unknown: Vec<String>,
    },
    /// The model checker could not determine if the specification holds or not.
    /// The vector contains the names of the specifications that are unknown
    UNKNOWN(Vec<String>),
}

impl ModelCheckerResult {
    /// Check whether the model checker returned safe
    pub fn is_safe(&self) -> bool {
        matches!(self, ModelCheckerResult::SAFE)
    }
}

/// Trait that needs to be implemented by an internal specification
/// representation
pub trait SpecificationTrait<C: ModelCheckerContext>: Sized + fmt::Debug {
    /// Error occurring when transformation from ELTL specification fails
    type TransformationError: error::Error + Sized;
    /// Internal specification type the model checker works on
    type InternalSpecType: Sized + TASpecification;

    /// Try to derive the specification type from ELTL specification
    ///
    /// Returns the translated specifications and the names of the properties
    /// that could not be translated, but should be reported as unknown.
    fn try_from_eltl(
        spec: impl Iterator<Item = (String, ELTLExpression)>,
        ctx: &C,
    ) -> Result<(Vec<Self>, Vec<String>), Self::TransformationError>;

    /// Create threshold automata to check
    ///
    /// This function allows to pair a specification with a threshold automaton.
    /// Each pair is labeled with the name of the property it belongs to.
    fn transform_threshold_automaton<TA: ThresholdAutomaton + ModifiableThresholdAutomaton>(
        ta: TA,
        specs: Vec<Self>,
        ctx: &C,
    ) -> Vec<(String, Self::InternalSpecType, TA)>;
}

/// Common trait implemented by specifications
///
/// This trait is mostly used in preprocessing to inform the preprocessor which
/// locations and variables appear in the specification, to ensure that they can
/// be treated separately
pub trait TASpecification: Display {
    /// Get the locations that appear in the specification
    ///
    /// This function can be used in the preprocessing to ensure no locations
    /// from the specification are removed
    fn locs_appearing(&self) -> impl IntoIterator<Item = &Location>;

    /// Get the variable constraints that appear in target
    ///
    /// This function can be used to get the interval constraints of variables
    /// in the target specification.
    fn var_constraint(&self) -> impl IntoIterator<Item = &LIAVariableConstraint>;
}

/// Trait that needs to be implemented by an internal threshold automaton
/// representation
pub trait TATrait<MC: ModelCheckerContext, SC>: ThresholdAutomaton + Sized + fmt::Debug {
    /// Error type that can occur when trying to convert from threshold automaton
    type TransformationError: error::Error;

    /// Try to derive the internal threshold automaton representation from a
    /// general threshold automaton
    fn try_from_general_ta(
        ta: GeneralThresholdAutomaton,
        ctx: &MC,
        spec_ctx: &SC,
    ) -> Result<Vec<Self>, Self::TransformationError>;
}

/// Trait of contexts for model checker
///
/// A context to a model checker supplies backend functionality such as, for
/// example an SMT solver to the model checker
pub trait ModelCheckerContext: Sized + Clone + fmt::Debug {
    /// Possible error that can occur during creation of the context
    type CreationError: error::Error;
    /// Options for the model checker context
    type ContextOptions;

    /// Create a new model checking context
    ///
    /// Tries to create a new context with the given options
    fn try_new(opt: Option<Self::ContextOptions>) -> Result<Self, Self::CreationError>;
}

/// Implement ModelCheckerContext for the SMT solver builder
impl ModelCheckerContext for SMTSolverBuilder {
    type CreationError = SMTSolverBuilderError;
    type ContextOptions = SMTSolverBuilderCfg;

    fn try_new(opt: Option<Self::ContextOptions>) -> Result<Self, Self::CreationError> {
        if let Some(cfg) = opt {
            return SMTSolverBuilder::new(&cfg);
        }
        SMTSolverBuilder::new_automatic_selection()
    }
}

/// Simple context for model checkers containing SMT solver and BDD manager
#[derive(Clone, Debug)]
pub struct SMTBddContext {
    /// Builder to construct new SMT solvers.
    smt_solver_builder: SMTSolverBuilder,
    /// The BDD manager to use for the model checking.
    bdd_manager: BDDManager,
}
impl SMTBddContext {
    /// returns the smt_solver_builder
    pub fn smt_solver_builder(&self) -> &SMTSolverBuilder {
        &self.smt_solver_builder
    }
    /// returns the bdd_manager
    pub fn bdd_manager(&self) -> &BDDManager {
        &self.bdd_manager
    }
}

impl ProvidesSMTSolverBuilder for SMTBddContext {
    fn get_solver_builder(&self) -> SMTSolverBuilder {
        self.smt_solver_builder.clone()
    }
}

impl ModelCheckerContext for SMTBddContext {
    type CreationError = SMTSolverBuilderError;

    type ContextOptions = (Option<SMTSolverBuilderCfg>, Option<BDDManagerConfig>);

    fn try_new(opt: Option<Self::ContextOptions>) -> Result<Self, Self::CreationError> {
        let (smt_cfg, bdd_cfg) = opt.unwrap_or((None, None));

        let bdd_mgr = bdd_cfg
            .map(|cfg| cfg.mgr_from_config())
            .unwrap_or_else(BDDManager::default);

        let smt_solver_builder = smt_cfg
            .map(|cfg| SMTSolverBuilder::new(&cfg))
            .unwrap_or_else(SMTSolverBuilder::new_automatic_selection)?;

        Ok(Self {
            smt_solver_builder,
            bdd_manager: bdd_mgr,
        })
    }
}

impl<C: ModelCheckerContext, SC> TATrait<C, SC> for GeneralThresholdAutomaton {
    type TransformationError = Infallible;

    fn try_from_general_ta(
        ta: GeneralThresholdAutomaton,
        _ctx: &C,
        _spec_ctx: &SC,
    ) -> Result<Vec<Self>, Self::TransformationError> {
        Ok(vec![ta])
    }
}

impl<C: ModelCheckerContext, SC> TATrait<C, SC> for LIAThresholdAutomaton {
    type TransformationError = LIATransformationError;

    fn try_from_general_ta(
        ta: GeneralThresholdAutomaton,
        _ctx: &C,
        _spec_ctx: &SC,
    ) -> Result<Vec<Self>, Self::TransformationError> {
        let lta = LIAThresholdAutomaton::try_from(ta)?;

        Ok(vec![lta])
    }
}

#[cfg(test)]
mod tests {
    use taco_smt_encoder::{SMTSolverBuilder, SMTSolverBuilderCfg};
    use taco_threshold_automaton::{
        BooleanVarConstraint, LocationConstraint, ParameterConstraint,
        expressions::{ComparisonOp, IntegerExpression, IntegerOp, Location, Parameter, Variable},
        general_threshold_automaton::{
            Action, GeneralThresholdAutomaton,
            builder::{GeneralThresholdAutomatonBuilder, RuleBuilder},
        },
        lia_threshold_automaton::LIAThresholdAutomaton,
    };

    use crate::TATrait;

    #[test]
    fn test_try_from_for_general_gta() {
        let ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
            .with_parameters(vec![
                Parameter::new("n"),
                Parameter::new("t"),
                Parameter::new("f"),
            ])
            .unwrap()
            .with_variables(vec![
                Variable::new("var1"),
                Variable::new("var2"),
                Variable::new("var3"),
            ])
            .unwrap()
            .with_locations(vec![
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
            ])
            .unwrap()
            .initialize()
            .with_initial_variable_constraints(vec![BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            )])
            .unwrap()
            .with_initial_location_constraints(vec![
                LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                    ComparisonOp::Eq,
                    Box::new(
                        IntegerExpression::Param(Parameter::new("n"))
                            - IntegerExpression::Param(Parameter::new("f")),
                    ),
                ) | LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ])
            .unwrap()
            .with_resilience_conditions(vec![ParameterConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::Const(3)),
                    IntegerOp::Mul,
                    Box::new(IntegerExpression::Atom(Parameter::new("f"))),
                )),
            )])
            .unwrap()
            .with_rules(vec![
                RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2"))
                    .with_actions(vec![
                        Action::new(
                            Variable::new("var1"),
                            IntegerExpression::Atom(Variable::new("var1")),
                        )
                        .unwrap(),
                    ])
                    .build(),
                RuleBuilder::new(1, Location::new("loc2"), Location::new("loc3"))
                    .with_guard(
                        BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Const(1)),
                        ) & BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Param(Parameter::new("n"))),
                        ),
                    )
                    .with_actions(vec![
                        Action::new(Variable::new("var3"), IntegerExpression::Const(0)).unwrap(),
                        Action::new(
                            Variable::new("var1"),
                            IntegerExpression::BinaryExpr(
                                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                                IntegerOp::Add,
                                Box::new(IntegerExpression::Const(1)),
                            ),
                        )
                        .unwrap(),
                    ])
                    .build(),
            ])
            .unwrap()
            .build();

        let ctx = SMTSolverBuilder::new(&SMTSolverBuilderCfg::new_z3()).unwrap();
        let got_ta = GeneralThresholdAutomaton::try_from_general_ta(ta.clone(), &ctx, &()).unwrap();

        assert_eq!(got_ta, vec![ta])
    }

    #[test]
    fn test_try_from_for_general_lta() {
        let ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
            .with_parameters(vec![
                Parameter::new("n"),
                Parameter::new("t"),
                Parameter::new("f"),
            ])
            .unwrap()
            .with_variables(vec![
                Variable::new("var1"),
                Variable::new("var2"),
                Variable::new("var3"),
            ])
            .unwrap()
            .with_locations(vec![
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
            ])
            .unwrap()
            .initialize()
            .with_initial_variable_constraints(vec![BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            )])
            .unwrap()
            .with_initial_location_constraints(vec![
                LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                    ComparisonOp::Eq,
                    Box::new(
                        IntegerExpression::Param(Parameter::new("n"))
                            - IntegerExpression::Param(Parameter::new("f")),
                    ),
                ) | LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ])
            .unwrap()
            .with_resilience_conditions(vec![ParameterConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::Const(3)),
                    IntegerOp::Mul,
                    Box::new(IntegerExpression::Atom(Parameter::new("f"))),
                )),
            )])
            .unwrap()
            .with_rules(vec![
                RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2"))
                    .with_actions(vec![
                        Action::new(
                            Variable::new("var1"),
                            IntegerExpression::Atom(Variable::new("var1")),
                        )
                        .unwrap(),
                    ])
                    .build(),
                RuleBuilder::new(1, Location::new("loc2"), Location::new("loc3"))
                    .with_guard(
                        BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Const(1)),
                        ) & BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Param(Parameter::new("n"))),
                        ),
                    )
                    .with_actions(vec![
                        Action::new(Variable::new("var3"), IntegerExpression::Const(0)).unwrap(),
                        Action::new(
                            Variable::new("var1"),
                            IntegerExpression::BinaryExpr(
                                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                                IntegerOp::Add,
                                Box::new(IntegerExpression::Const(1)),
                            ),
                        )
                        .unwrap(),
                    ])
                    .build(),
            ])
            .unwrap()
            .build();

        let ctx = SMTSolverBuilder::new(&SMTSolverBuilderCfg::new_z3()).unwrap();
        let got_ta = LIAThresholdAutomaton::try_from_general_ta(ta.clone(), &ctx, &()).unwrap();

        let lta = ta.try_into().unwrap();

        assert_eq!(got_ta, vec![lta])
    }
}
