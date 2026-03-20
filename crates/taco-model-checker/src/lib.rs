//! This module contains the different model checkers that are available in
//! TACO.
//! Every model checker needs to implement the [`ModelChecker`] trait.

use core::fmt;
use std::{error, fmt::Display};

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
pub mod preprocessing;
pub mod reachability_specification;

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
    type ThresholdAutomatonType: TATrait<
            Self::ModelCheckerContext,
            <Self::SpecType as SpecificationTrait<Self::ModelCheckerContext>>::InternalSpecType,
        >;

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
    #[allow(clippy::type_complexity)]
    fn initialize(
        opts: Self::ModelCheckerOptions,
        ta_spec: Vec<
            (
                <<Self as ModelChecker>::SpecType as SpecificationTrait<
                    Self::ModelCheckerContext,
                >>::InternalSpecType,
                Vec<Self::ThresholdAutomatonType>,
            ),
        >,
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
    #[allow(clippy::type_complexity)]
    fn new(
        ctx_opts: Option<
            <<Self as ModelChecker>::ModelCheckerContext as ModelCheckerContext>::ContextOptions,
        >,
        mc_opts: Self::ModelCheckerOptions,
        preprocessors: Vec<Box<dyn Preprocessor<GeneralThresholdAutomaton, <Self::SpecType as SpecificationTrait<Self::ModelCheckerContext>>::InternalSpecType, Self::ModelCheckerContext>>>,
        ta: GeneralThresholdAutomaton,
        spec: impl Iterator<Item = (String, ELTLExpression)>,
    ) -> Result<
        Self,
        ModelCheckerSetupError<
            <<Self as ModelChecker>::ThresholdAutomatonType as TATrait<
                Self::ModelCheckerContext, <Self::SpecType as SpecificationTrait<Self::ModelCheckerContext>>::InternalSpecType,
            >>::TransformationError,
            <<Self as ModelChecker>::SpecType as SpecificationTrait<
                Self::ModelCheckerContext,
            >>::TransformationError,
            <<Self as ModelChecker>::ModelCheckerContext as ModelCheckerContext>::CreationError,
            Self::InitializationError,
        >,
    >{
        let ctx = Self::ModelCheckerContext::try_new(ctx_opts);
        if let Err(ctx_err) = ctx {
            return Err(ModelCheckerSetupError::ErrorContextSetup(ctx_err));
        }
        let ctx = ctx.unwrap();

        let spec = Self::SpecType::try_from_eltl(spec, &ctx);
        if let Err(spec_err) = spec {
            return Err(ModelCheckerSetupError::ErrorTransformingSpec(spec_err));
        }
        let spec = spec.unwrap();

        // Combine the specification with the threshold automaton
        let ta_spec = Self::SpecType::transform_threshold_automaton(ta, spec, &ctx);

        let ta_spec = ta_spec
            .into_iter()
            .map(|(spec, mut ta)| {
                // Preprocessing on tas with information from the specification
                for processor in preprocessors.iter() {
                    processor.process(&mut ta, &spec, &ctx);
                }

                trace!("Threshold automaton for property {spec} after preprocessing: {ta}");

                let ta = Self::ThresholdAutomatonType::try_from_general_ta(ta, &ctx, &spec)?;

                Ok((spec, ta))
            })
            .collect::<Result<Vec<_>, _>>();
        if let Err(ta_err) = ta_spec {
            return Err(ModelCheckerSetupError::ErrorTransformingTA(ta_err));
        }
        let ta_spec = ta_spec.unwrap();

        let mc = Self::initialize(mc_opts, ta_spec, ctx.clone());
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
#[derive(Debug, Clone, PartialEq)]
pub enum ModelCheckerSetupError<
    TE: error::Error,
    SE: error::Error,
    CE: error::Error,
    IE: error::Error,
> {
    /// Could not initialize model checker because transformation of threshold
    /// automaton failed
    ErrorTransformingTA(TE),
    /// Could not initialize model checker because transformation of
    /// specification failed
    ErrorTransformingSpec(SE),
    /// Could not initialize model checker because context could not be initialized
    ErrorContextSetup(CE),
    /// Error that can occur during initialization
    ErrorInitializingModelChecker(IE),
}

impl<TE, SE, CE, IE> fmt::Display for ModelCheckerSetupError<TE, SE, CE, IE>
where
    TE: error::Error,
    SE: error::Error,
    CE: error::Error,
    IE: error::Error,
{
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

impl<TE, SE, CE, IE> error::Error for ModelCheckerSetupError<TE, SE, CE, IE>
where
    TE: error::Error,
    SE: error::Error,
    CE: error::Error,
    IE: error::Error,
{
}

/// Result type for a model checking run
#[derive(Debug, Clone, PartialEq)]
pub enum ModelCheckerResult {
    /// Threshold automaton fulfills all specifications
    SAFE,
    /// Threshold automaton does not fulfill the specification
    ///
    /// The string contains the name of the violated specification and the path
    /// is a concrete error path that serves as an example for the violation
    UNSAFE(Vec<(String, Box<Path>)>),
    /// Model checker could not determine if the specification holds or not
    ///
    /// The vector contains the names of the specifications for which the result
    /// could not be determined.
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
    type InternalSpecType: Sized + TargetSpec;

    /// Try to derive the specification type from ELTL specification
    fn try_from_eltl(
        spec: impl Iterator<Item = (String, ELTLExpression)>,
        ctx: &C,
    ) -> Result<Vec<Self>, Self::TransformationError>;

    /// Create threshold automata to check
    ///
    /// This function allows to pair a specification with a threshold automaton
    fn transform_threshold_automaton<TA: ThresholdAutomaton + ModifiableThresholdAutomaton>(
        ta: TA,
        specs: Vec<Self>,
        ctx: &C,
    ) -> Vec<(Self::InternalSpecType, TA)>;
}

/// Common trait implemented by types that specify a target configuration
/// in model checking
///
/// This trait is mostly used in preprocessing to ensure target locations are not
/// removed by accident
pub trait TargetSpec: Display {
    /// Get the locations that appear in the target
    ///
    /// This function can be used in the preprocessing to ensure no locations
    /// from the specification are removed
    fn get_locations_in_target(&self) -> impl IntoIterator<Item = &Location>;

    /// Get the variable constraints that appear in target
    ///
    /// This function can be used to get the interval constraints of variables
    /// in the target specification.
    fn get_variable_constraint(&self) -> impl IntoIterator<Item = &LIAVariableConstraint>;
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
    type TransformationError = DummyError;

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

/// Error that should never be built
#[derive(Debug)]
pub struct DummyError {}

impl fmt::Display for DummyError {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        unreachable!("This error should never have been built")
    }
}

impl error::Error for DummyError {}

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
