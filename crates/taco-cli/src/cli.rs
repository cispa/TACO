//! Command Line Interface for TACO
//!
//! TACO uses the `clap` crate to parse command line arguments and create the
//! CLI interface. This module defines all available commands and options (and
//! their documentation) as well as some utility functions to apply these
//! options.

use std::result::Result::Ok;
use std::{fmt::Display, fs, io, path::PathBuf, process::exit};

use anyhow::{Context, anyhow};

use clap::{Args, Parser, Subcommand, ValueEnum};
use taco_bdd::BDDManagerConfig;

use log::{LevelFilter, error, info};
use log4rs::{
    Config,
    append::console::ConsoleAppender,
    config::{Appender, Root},
    encode::pattern::PatternEncoder,
};
use taco_acs_model_checker::ACSModelChecker;
use taco_display_utils::join_iterator;
use taco_model_checker::preprocessing::ExistingPreprocessors;
use taco_model_checker::{
    ModelChecker,
    eltl::{ELTLExpression, ELTLSpecification},
    preprocessing::{self},
};
use taco_model_checker::{ModelCheckerContext, ModelCheckerResult, TASpecification};
use taco_parser::{ParseTAWithLTL, bymc::ByMCParser, tla::TLAParser};
use taco_smt_encoder::{ProvidesSMTSolverBuilder, SMTSolverBuilderCfg};

use taco_smt_model_checker::{SMTModelChecker, SMTModelCheckerOptions};
use taco_threshold_automaton::{
    ModifiableThresholdAutomaton, ThresholdAutomaton,
    expressions::{Atomic, BooleanExpression, ComparisonOp, IntegerExpression, Location, Variable},
    general_threshold_automaton::GeneralThresholdAutomaton,
};
use taco_zcs_model_checker::{ZCSModelChecker, ZCSModelCheckerHeuristics};

use crate::cli::output_formats::{into_bymc, into_tla};
use crate::{cli, taco_config::TACOConfig};

mod output_formats;

/// Preprocessors that will be used by default
pub const DEFAULT_PREPROCESSORS: [ExistingPreprocessors; 5] = [
    ExistingPreprocessors::DropSelfLoops,
    ExistingPreprocessors::DropUnreachableLocations,
    ExistingPreprocessors::RemoveUnusedVariables,
    ExistingPreprocessors::CheckInitCondSatSMT,
    ExistingPreprocessors::ReplaceTrivialGuardsSMT,
];

/// TACO toolsuite for threshold automata  - Command Line Interface
///
/// This is the command line interface for the TACO toolsuite for threshold
/// automata. You can use the --help / -h flag to get all available commands and
/// options.
/// For more advanced configuration options, an introduction into the different
/// specification formats and an introduction into the formal model of threshold
/// automata, visit the TACO homepage:
///
///     https://taco-mc.dev
///
/// If you have any questions or you encounter bugs, feel free to open an issue
/// on TACO's GitHub repository:
///
///     https://github.com/cispa/TACO/issues/new/choose
///
///
#[derive(Parser, Debug)]
#[command(version, name = "TACO CLI", about, long_about)]
pub(crate) struct Cli {
    #[command(flatten)]
    pub(crate) log_config: LoggerConfig,
    #[command(subcommand)]
    pub(crate) command: Commands,
}

#[derive(Subcommand, Debug)]
pub enum Commands {
    /// Read the specification file and check the specified properties
    Check {
        #[command(flatten)]
        input: SpecFileInput,

        /// Configuration file for the model checker
        #[arg(short, long, value_name = "CONFIG_FILE")]
        config_file: Option<PathBuf>,

        /// Request a specific model checker to be used
        #[command(subcommand)]
        model_checker: Option<ModelCheckerOption>,

        /// Configure the BDD library to use
        #[arg(short, long, value_name = "BDD")]
        bdd: Option<BDDManagerOption>,

        /// Select the SMT solver to be used
        #[arg(short, long, value_name = "SMT_SOLVER")]
        smt_solver: Option<SMTSolverDefaultOptions>,

        /// Enable compact output of error paths omitting locations with 0
        /// processes and variables that are 0
        #[arg(short = 'o', long, default_value_t = false)]
        compact_out: bool,

        /// Abort the model checking on the first counter example that has been
        /// found
        #[arg(short, long, default_value_t = false)]
        abort_on_violation: bool,

        /// Choose the mode with which to run the check
        #[arg(long, value_enum, default_value_t = CheckMode::Normal)]
        mode: CheckMode,
    },
    #[cfg(feature = "dot")]
    /// Read the specification file and visualize the threshold automaton
    Visualize {
        #[command(flatten)]
        input: SpecFileInput,

        #[command(flatten)]
        output: VisualizationOutput,
    },
    /// Translate from one specification file format to another one
    Translate {
        #[command(flatten)]
        input: SpecFileInput,

        #[command(flatten)]
        output: TranslationOutput,
    },
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum CheckMode {
    /// Normal model checking, given the ta and spec from the input file
    /// (default)
    Normal,
    /// Coverability check through the CLI
    Coverability,
    /// Reachability check through the CLI
    Reachability,
}

#[derive(Args, Debug)]
pub(crate) struct SpecFileInput {
    /// Location and name of the specification file
    input_file: PathBuf,

    /// Format of the input specification file (if the file ending is not `.ta`,
    /// `.eta`, `.tla`)
    #[arg(short, long, value_name = "INPUT_FORMAT")]
    format: Option<SpecFileFormat>,
}

#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum SpecFileFormat {
    /// Specification file format introduced by ByMC (usually `.ta` or `.eta` files)
    BYMC,
    /// TLA+ specification (usually `.tla` files)
    TLA,
}

impl Display for SpecFileFormat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SpecFileFormat::BYMC => write!(f, "ByMC"),
            SpecFileFormat::TLA => write!(f, "TLA+"),
        }
    }
}

#[derive(Subcommand, Debug, Copy, Clone, PartialEq, Eq, PartialOrd)]
pub(crate) enum ModelCheckerOption {
    /// Symbolic model checker
    Zcs {
        /// Select a heuristics for the symbolic model checker
        #[arg(long, value_name = "HEURISTICS")]
        heuristic: Option<SymbolicModelCheckerHeuristics>,
    },
    /// SMT based model checker
    Smt {
        /// Enable parallel model checking (default: false / off)
        #[arg(short, long, value_name = "PARALLEL", default_value_t = false)]
        parallel: bool,
    },
    /// Counter system based model checker
    Acs,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub(crate) enum SymbolicModelCheckerHeuristics {
    /// This heuristics yields a semi-decision procedure by unfolding cycles if
    /// the input TA contains resets but no decrements. It can be used to verify
    /// extended threshold automata for coverability or reachability
    /// specifications.
    ResetHeuristics,
    /// This heuristics yields a semi-decision procedure by unfolding cycles if
    /// the input TA contains increments and decrements. It can be used to
    /// verify extended threshold automata for coverability or reachability
    /// specifications.
    DecrementAndIncrementHeuristics,
    /// This heuristics yields a decision procedure by only traversing cycles
    /// once. It can be used to verify canonical threshold automata (no
    /// resets/decrements) for coverability or reachability specifications.
    CanonicalHeuristics,
    /// This is a greedy heuristics that only checks if the symbolic error graph
    /// is empty. It is neither complete nor sound but guarantees termination.
    /// If the error graph is empty the property holds, otherwise no conclusion
    /// can be drawn.
    EmptyErrorGraphHeuristic,
}

#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub(crate) enum BDDManagerOption {
    /// CUDD BDD library
    #[cfg(feature = "cudd")]
    CUDD,
    /// OxiDD BDD library
    #[cfg(feature = "oxidd")]
    OXIDD,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
/// SMT solvers that are supported by default
pub enum SMTSolverDefaultOptions {
    /// Z3 SMT solver
    Z3,
    /// CVC5 SMT solver
    CVC5,
}

#[derive(Debug, Args)]
pub struct VisualizationOutput {
    /// Output file to save the visualization
    output_file: PathBuf,
    /// Output format for the visualization
    ///
    /// Supported formats are: `dot`, `svg`, `png`; default is `dot`
    /// Note that `svg` and `png` formats require the `graphviz` library to be
    /// installed on the system
    #[arg(short, long, value_name = "OUT_FORMAT", default_value = "dot")]
    output_format: OutputFormat,
}

#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum OutputFormat {
    /// Output as DOT
    DOT,
    /// Output as SVG
    SVG,
    /// Output as PNG
    PNG,
}

#[derive(Debug, Args)]
pub struct TranslationOutput {
    /// Output file to save the translated output to
    output_file: PathBuf,
    /// Format to translate to (default: ByMC)
    #[arg(short, long, value_name = "OUT_FORMAT", default_value = "bymc")]
    output_format: SpecFileFormat,
}

#[derive(Debug, Args)]
pub(crate) struct LoggerConfig {
    /// Read the logger configuration from file.
    /// Logger configuration can be provided in the log4rs specification format.
    #[arg(long)]
    logger_config_file: Option<String>,

    /// Enable debug output.
    /// **Note**: This flag must be passed first, before any command.
    #[arg(short, long, default_value_t = false)]
    debug: bool,
}

/// Initialize the logger as specified in `cfg`
///
/// By default the logger is configured to log to stdout. If a log4rs
/// configuration file is given in `cfg`, the configuration from that file will
/// be used instead
pub(crate) fn initialize_logger(cfg: LoggerConfig) -> Result<(), anyhow::Error> {
    if let Some(f) = cfg.logger_config_file {
        // Read logger configuration file
        log4rs::init_file(f, Default::default())
            .with_context(|| "Failed to read logger config file")?;
        return Ok(());
    }

    let p_encoder = match cfg.debug {
        true => PatternEncoder::new("{d(%Y-%m-%d %H:%M:%S)} - {h({l})} - [{f}:{L} - {M}] - {m}{n}"),
        false => PatternEncoder::new("{d(%H:%M:%S)} - {h({l})} - {m}{n}"),
    };

    // Log to stdout
    let stdout = ConsoleAppender::builder()
        .encoder(Box::new(p_encoder))
        .build();

    let mut level = LevelFilter::Info;
    if cfg.debug {
        level = LevelFilter::Debug;
    }

    let log_config = Config::builder()
        .appender(Appender::builder().build("stdout", Box::new(stdout)))
        .build(Root::builder().appender("stdout").build(level))
        .expect("Failed to initialize logger");

    log4rs::init_config(log_config).expect("Failed to initialize console logger");
    Ok(())
}

/// Get SMT solver configuration based on selected solver
pub(crate) fn get_smt_solver(smt_config: SMTSolverDefaultOptions) -> SMTSolverBuilderCfg {
    match smt_config {
        SMTSolverDefaultOptions::Z3 => SMTSolverBuilderCfg::new_z3(),
        SMTSolverDefaultOptions::CVC5 => SMTSolverBuilderCfg::new_cvc5(),
    }
}

/// Get BDD manager configuration based on selected BDD manager
pub(crate) fn get_bdd_manager_cfg(bdd: BDDManagerOption) -> BDDManagerConfig {
    match bdd {
        #[cfg(feature = "cudd")]
        BDDManagerOption::CUDD => BDDManagerConfig::new_cudd(),
        #[cfg(feature = "oxidd")]
        BDDManagerOption::OXIDD => BDDManagerConfig::new_oxidd(),
    }
}

/// Get the symbolic model checker heuristic based on the CLI option
fn get_zcs_model_checker_heuristic(
    heuristic: Option<SymbolicModelCheckerHeuristics>,
) -> Option<ZCSModelCheckerHeuristics> {
    heuristic.map(|h| match h {
        SymbolicModelCheckerHeuristics::ResetHeuristics => {
            ZCSModelCheckerHeuristics::ResetHeuristics
        }
        SymbolicModelCheckerHeuristics::DecrementAndIncrementHeuristics => {
            ZCSModelCheckerHeuristics::DecrementAndIncrementHeuristics
        }
        SymbolicModelCheckerHeuristics::CanonicalHeuristics => {
            ZCSModelCheckerHeuristics::CanonicalHeuristics
        }
        SymbolicModelCheckerHeuristics::EmptyErrorGraphHeuristic => {
            ZCSModelCheckerHeuristics::EmptyErrorGraphHeuristics
        }
    })
}

/// Constructs the preprocessors, either from the configuration file or just
/// uses the default preprocessors specified in [DEFAULT_PREPROCESSORS]
fn get_preprocessors<S, C>(
    cfg: &TACOConfig,
) -> Vec<Box<dyn preprocessing::Preprocessor<GeneralThresholdAutomaton, S, C>>>
where
    S: TASpecification,
    C: ModelCheckerContext + ProvidesSMTSolverBuilder,
{
    if cfg.get_preprocessors_cfg().is_some() {
        info!(
            "Configured TACO to use preprocessors: {}",
            join_iterator(cfg.get_preprocessors_cfg().clone().unwrap().iter(), ", ")
        );
    }

    cfg.get_preprocessors_cfg()
        .clone()
        .unwrap_or(DEFAULT_PREPROCESSORS.to_vec())
        .into_iter()
        .map(|mc| mc.into())
        .collect()
}

/// Initialize the symbolic model checker with the given options,
/// threshold automaton and specifications
pub(crate) fn initialize_zcs_model_checker(
    mc_cfg: Option<SymbolicModelCheckerHeuristics>,
    ta: GeneralThresholdAutomaton,
    spec: ELTLSpecification,
    cfg: TACOConfig,
) -> ZCSModelChecker {
    let opt = get_zcs_model_checker_heuristic(mc_cfg);

    let preprocessors = get_preprocessors(&cfg);

    let mc = ZCSModelChecker::new(
        Some(cfg.get_bdd_smt_config()),
        opt,
        preprocessors,
        ta,
        spec.into_iter(),
    );

    if let Err(err) = mc {
        error!("Error during initialization of the model checker: {}", err);
        exit(1);
    }

    mc.unwrap()
}

pub(crate) fn initialize_smt_model_checker(
    ta: GeneralThresholdAutomaton,
    spec: ELTLSpecification,
    cfg: TACOConfig,
    parallel: bool,
) -> SMTModelChecker {
    let opts = SMTModelCheckerOptions::new(parallel);

    let preprocessors = get_preprocessors(&cfg);

    let mc = SMTModelChecker::new(
        cfg.get_smt_solver_builder_cfg(),
        opts,
        preprocessors,
        ta,
        spec.into_iter(),
    );

    if let Err(err) = mc {
        error!("Error during initialization of the model checker: {}", err);
        exit(1);
    }

    mc.unwrap()
}

pub(crate) fn initialize_cs_model_checker(
    ta: GeneralThresholdAutomaton,
    spec: ELTLSpecification,
    cfg: TACOConfig,
) -> ACSModelChecker {
    let preprocessors = get_preprocessors(&cfg);

    let mode = None;

    let mc = ACSModelChecker::new(
        cfg.get_smt_solver_builder_cfg(),
        mode,
        preprocessors,
        ta,
        spec.into_iter(),
    );

    if let Err(err) = mc {
        error!("Error during initialization of the model checker: {}", err);
        exit(1);
    }

    mc.unwrap()
}

/// Parse the input file into a threshold automaton
///
/// This tries to open the file given by `SpecFileInput` and tries to format it
/// according to the format specified. If no format is specified, tries to
/// detect the file ending, otherwise uses ByMC by default.
pub(crate) fn parse_input_file(
    cfg: SpecFileInput,
) -> Result<(GeneralThresholdAutomaton, ELTLSpecification), anyhow::Error> {
    let mut format = cfg.format;

    if format.is_none()
        && let Some(ext) = cfg.input_file.extension()
    {
        let ext = ext.to_str().unwrap();
        if ext == "ta" || ext == "eta" {
            format = Some(SpecFileFormat::BYMC);
        }
        if ext == "tla" {
            format = Some(SpecFileFormat::TLA);
        }
    }

    let f =
        fs::read_to_string(cfg.input_file).with_context(|| "Unable to read specification file")?;

    match format {
        None | Some(SpecFileFormat::BYMC) => ByMCParser::new().parse_ta_and_spec(&f),
        Some(SpecFileFormat::TLA) => TLAParser::new().parse_ta_and_spec(&f),
    }
}

/// Visualize the threshold automaton in the given format
///
/// When `svg` or `png` format is selected, the `graphviz` library must be
/// installed on the system.
#[cfg(feature = "dot")]
pub(crate) fn visualize_ta(
    ta: &GeneralThresholdAutomaton,
    cfg: VisualizationOutput,
) -> Result<(), anyhow::Error> {
    use std::{
        borrow::BorrowMut,
        process::{Command, Stdio},
    };

    use anyhow::Context;
    use taco_threshold_automaton::dot::ToDOT;
    let out_str = ta.get_dot_graph();

    let out_arg = match cfg.output_format {
        OutputFormat::DOT => {
            fs::write(cfg.output_file, out_str).with_context(|| "Failed to write output file")?;
            return Ok(());
        }
        OutputFormat::SVG => "-Tsvg",
        OutputFormat::PNG => "-Tpng",
    };

    if Command::new("dot")
        .arg("--version")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .is_err()
    {
        return Err(anyhow!("Graphviz is not installed on the system"));
    }

    let mut echo_cmd = Command::new("echo")
        .arg(out_str)
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();

    let _ = echo_cmd.borrow_mut().wait();

    let _ = Command::new("dot")
        .stdin(echo_cmd.stdout.unwrap())
        .arg(out_arg)
        .arg("-o")
        .arg(cfg.output_file)
        .output()
        .with_context(|| "Failed to execute graphviz")?;

    Ok(())
}

fn model_check_ta(
    ta: GeneralThresholdAutomaton,
    spec: ELTLSpecification,
    model_checker: Option<ModelCheckerOption>,
    config: TACOConfig,
    abort_on_violation: bool,
) -> ModelCheckerResult {
    match model_checker.unwrap_or_else(|| {
        if ta.has_resets() || ta.has_decrements() {
            return ModelCheckerOption::Zcs { heuristic: None };
        }

        ModelCheckerOption::Smt { parallel: false }
    }) {
        cli::ModelCheckerOption::Zcs { heuristic } => {
            let res = initialize_zcs_model_checker(heuristic, ta, spec, config)
                .verify(abort_on_violation);

            if let Err(err) = res {
                error!(
                    "An error occurred during the model checking with the symbolic model checker: {}",
                    err
                );
                exit(1);
            }

            res.unwrap()
        }
        cli::ModelCheckerOption::Smt { parallel } => {
            let res =
                initialize_smt_model_checker(ta, spec, config, parallel).verify(abort_on_violation);
            if let Err(err) = res {
                error!(
                    "An error occurred during the model checking with the SMT model checker: {}",
                    err
                );
                exit(1)
            }

            res.unwrap()
        }
        cli::ModelCheckerOption::Acs => {
            let res = initialize_cs_model_checker(ta, spec, config).verify(abort_on_violation);

            if let Err(err) = res {
                error!(
                    "An error occurred during the model checking with the CS model checker: {}",
                    err
                );
                exit(1)
            }

            res.unwrap()
        }
    }
}

pub fn display_result(
    ta: GeneralThresholdAutomaton,
    spec: ELTLSpecification,
    model_checker: Option<ModelCheckerOption>,
    config: TACOConfig,
    abort_on_violation: bool,
    mode: CheckMode,
    compact_out: bool,
) {
    let res = model_check_ta(ta, spec, model_checker, config, abort_on_violation);

    match mode {
        // If we find a counter-example for the specification [](negated goal configuration) for coverability or reachability,
        // We return this as the path that we were looking for.
        cli::CheckMode::Coverability | cli::CheckMode::Reachability => match res {
            taco_model_checker::ModelCheckerResult::SAFE => {
                info!(
                    "The provided configuration is not reachable from the initial configuration. Coverability/Reachability property not satisfied."
                )
            }
            taco_model_checker::ModelCheckerResult::UNSAFE {
                violations,
                unknown,
            } => {
                for (property, error_path) in violations {
                    if compact_out {
                        info!(
                            "Path towards the desired configuration of our property: '{property}': {}",
                            error_path.display_compact()
                        );
                    } else {
                        info!(
                            "Path towards the desired configuration of our property: '{property}': {error_path}\n"
                        )
                    }
                }
                for property in unknown {
                    info!(
                        "The configured model checker could not determine whether the threshold automaton satisfies property: {property}"
                    );
                }
            }
            taco_model_checker::ModelCheckerResult::UNKNOWN(unknown) => {
                for property in unknown {
                    info!(
                        "The configured model checker could not determine whether the threshold automaton satisfies property: {property}"
                    );
                }
            }
        },
        _ => match res {
            taco_model_checker::ModelCheckerResult::SAFE => {
                info!("Threshold automaton satisfies all properties. The protocol is safe.")
            }
            taco_model_checker::ModelCheckerResult::UNSAFE {
                violations,
                unknown,
            } => {
                for (property, error_path) in violations {
                    if compact_out {
                        info!(
                            "Counter example to property '{property}': {}",
                            error_path.display_compact()
                        );
                    } else {
                        info!("Counter example to property '{property}': {error_path}\n")
                    }
                }
                for property in unknown {
                    info!(
                        "The configured model checker could not determine whether the threshold automaton satisfies property: {property}"
                    );
                }
                info!("The protocol is unsafe.")
            }
            taco_model_checker::ModelCheckerResult::UNKNOWN(unknown) => {
                for property in unknown {
                    info!(
                        "The configured model checker could not determine whether the threshold automaton satisfies property: {property}"
                    );
                }
            }
        },
    }
}

pub fn parse_coverability(ta: &mut GeneralThresholdAutomaton) -> String {
    let mut loc_name = String::new();
    loop {
        println!(
            "Please input the name of the location that should be covered in your coverability check:"
        );
        loc_name.clear();
        io::stdin().read_line(&mut loc_name).unwrap();

        // Check whether this location is actually in the ta
        if ta
            .locations()
            .any(|l| l.name() == Location::new(loc_name.trim()).name())
        {
            break;
        }
        println!(
            "Location '{}' does not exist in the threshold automaton!",
            loc_name.trim()
        );
        let all_locations: Vec<&str> = ta.locations().map(|l| l.name()).collect();
        println!("Possible locations are : {}", all_locations.join(", "))
    }
    // Ask for the initial locations
    parse_initial_configuration(ta);

    println!(
        "Checking whether location '{}' can be covered in the threshold automaton.",
        loc_name
    );
    loc_name
}

/// The coverability specification looks as follows:
/// We want to find a path from an initial configuration to a configuration where the location is covered
/// Thus the specification looks as follows:
/// (expression_initial) => [](to_be_covered_loc = 0)
/// Since the initial configuration is coded into the ta, there is no need for the implication.
/// A counter example to this specification is exactly the path we are looking for
pub fn create_coverability_expression(loc_name: String) -> ELTLExpression {
    ELTLExpression::Globally(Box::new(ELTLExpression::LocationExpr(
        Box::new(IntegerExpression::Atom(Location::new(loc_name.trim()))),
        ComparisonOp::Eq,
        Box::new(IntegerExpression::Const(0)),
    )))
}

pub fn parse_reachability(ta: &mut GeneralThresholdAutomaton) -> (Vec<String>, Vec<String>) {
    // Ask for the reachability specification
    let mut populated_locs: Vec<String> = Vec::new();
    loop {
        println!(
            "Input the name of a location that should be covered by processes or press enter when you have input all of them."
        );
        let mut loc_name = String::new();
        io::stdin().read_line(&mut loc_name).unwrap();

        // Check at least one location has been input
        if populated_locs.is_empty() && loc_name.trim().is_empty() {
            println!("Please input at least one location that should be populated.");
            continue;
        }
        // Leave the input loop when enter was pressed and at least one valid location was input
        if loc_name.trim().is_empty() {
            break;
        }

        // Check that the location hasn't been input before
        if populated_locs.contains(&loc_name.trim().to_string()) {
            println!("You have already specified this location.");
            continue;
        }
        // Check that the location is actually in the ta
        if !ta
            .locations()
            .any(|l| l.name() == Location::new(loc_name.trim()).name())
        {
            println!(
                "Location '{}' does not exist in the threshold automaton!",
                loc_name.trim()
            );
            let all_locations: Vec<&str> = ta.locations().map(|l| l.name()).collect();
            println!("Possible locations are : {}", all_locations.join(", "));
            continue;
        }

        populated_locs.push(loc_name.trim().to_string());
    }

    // Compute the unpopulated locations
    let unpopulated_locs: Vec<String> = ta
        .locations()
        .filter(|l| !populated_locs.contains(&l.name().to_string()))
        .map(|name| name.to_string())
        .collect();

    // Ask for the initial configuration
    parse_initial_configuration(ta);

    println!(
        "Checking whether the specified configuration can be reached in the threshold automaton. The configuration looks as follows: locations to be populated: {}, and locations to be unpopulated: {}",
        populated_locs.join(", "),
        unpopulated_locs.join(", ")
    );
    (populated_locs, unpopulated_locs)
}

/// The reachability specification looks as follows:
/// We want to find a path from an initial configuration to a specific configuration
/// Thus the specification looks as follows:
/// (expression_initial) =>
/// []((pop_loc_1 = 0) || ... || (pop_loc_p = 0) || (unpop_loc_1 > 0) || ... || (unpop_loc_u > 0)
/// Since the initial configuration is coded into the ta, there is no need for the implication.
/// A counter example to this specification is exactly the path we are looking for
pub fn create_reachability_expression(
    populated_locs: Vec<String>,
    unpopulated_locs: Vec<String>,
) -> ELTLExpression {
    let populated_expression = populated_locs
        .iter()
        .map(|v| {
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new(v))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            ))
        })
        .reduce(|acc, val| Box::new(ELTLExpression::And(acc, val)))
        .unwrap();

    let unpopulated_expression = unpopulated_locs
        .iter()
        .map(|v| {
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new(v))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(0)),
            ))
        })
        .reduce(|acc, val| Box::new(ELTLExpression::And(acc, val)))
        .unwrap();

    ELTLExpression::Globally(Box::new(ELTLExpression::Or(
        populated_expression,
        unpopulated_expression,
    )))
}

fn parse_initial_configuration(ta: &mut GeneralThresholdAutomaton) {
    println!(
        "Do you want to manually input an initial configuration? [y/n] If not, the initial locations and the initial variable valuations specified in the provided .ta file will be used."
    );
    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    let input = input.trim().to_lowercase();

    if !(input == "y" || input == "yes") {
        println!(
            "Using the initial locations and initial variable constraints provided in the .ta file."
        );
        return;
    }

    println!(
        "Please input the number of processes in each location for your initial configuration:"
    );
    let mut location_constraints = Vec::new();
    for loc in ta.locations() {
        let procs_in_loc = loop {
            println!("{}:", loc.name());
            let mut num = String::new();
            io::stdin().read_line(&mut num).unwrap();
            match num.trim().parse::<u32>() {
                Ok(num) => break num,
                _ => println!("Invalid input. Please enter a number greater or equal to 0."),
            }
        };
        location_constraints.push(BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Location::new(loc.name()))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(procs_in_loc)),
        ));
    }
    ta.replace_initial_location_constraints(location_constraints);

    println!("Please input the initial variable valuations:");
    let mut variable_constraints = Vec::new();
    for var in ta.variables() {
        let var_value = loop {
            println!("{}:", var.name());
            let mut num = String::new();
            io::stdin().read_line(&mut num).unwrap();
            match num.trim().parse::<u32>() {
                Ok(num) => break num,
                _ => println!("Invalid input. Please enter a number greater or equal to 0."),
            }
        };
        variable_constraints.push(BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Variable::new(var.name()))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(var_value)),
        ));
    }
    ta.replace_initial_variable_constraints(variable_constraints);
}

/// Translate a threshold automaton into the specified format and write the
/// resulting specification to the specified output file
pub(crate) fn translate_ta(
    ta: &GeneralThresholdAutomaton,
    spec: &ELTLSpecification,
    out: TranslationOutput,
) -> Result<(), anyhow::Error> {
    let translated_str: String = match out.output_format {
        SpecFileFormat::BYMC => into_bymc(ta, spec),
        SpecFileFormat::TLA => into_tla(ta, spec),
    };

    fs::write(out.output_file, translated_str).with_context(|| "Failed to write output file")?;
    info!("Finished writing output file");

    Ok(())
}
