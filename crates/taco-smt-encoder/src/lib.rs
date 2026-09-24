//! Interface to interact with SMT solvers
//!
//! The module mostly reuses the [easy-smt](https://crates.io/crates/easy-smt)
//! crate to interact with the SMT solvers. Easy-smt starts SMT solvers by
//! starting the SMT solver as a subprocess in interactive mode.
//! This crate provides a higher-level interface to encode boolean expressions
//! and utility functions to start and configure popular SMT solvers.

use core::{error, fmt};
use std::{io::Write, process::Command};

use easy_smt::{Context, ContextBuilder};
use expression_encoding::SMTSolverError;
use log::{debug, error, trace, warn};

#[cfg(feature = "config_deserialize")]
use serde::Deserialize;

pub mod expression_encoding;

/// Z3 command
pub const Z3_PRG: &str = "z3";
/// Option to set Z3 in SMT-LIB2 language and interactive mode
pub const Z3_ARGS: [&str; 3] = ["-smt2", "-in", "-v:0"];

/// cvc5 command
pub const CVC5_PRG: &str = "cvc5";
/// Option to set CVC5 in quiet mode, use SMT-LIB2 language and force logic to LIA
pub const CVC5_ARGS: [&str; 3] = ["--quiet", "--lang=smt2", "--incremental"];

/// Interface to interact with SMT solver
///
/// This type is an alias for the `easy_smt::Context` type. See
/// [easy-smt](https://crates.io/crates/easy-smt) for more information.
pub type SMTSolver = Context;

/// SMT expression
///
/// This type is an alias for the [`easy_smt::SExpr`] type.
pub type SMTExpr = easy_smt::SExpr;

/// Type for functions that check the compatibility of the SMT solver version
///
/// This function takes the version of the SMT solver as a tuple of major, minor
/// and patch version.
///
/// The function should take care of warning the user if the version is not
/// compatible with the current version of the library. Warnings should be
/// output using the `warn` or `error` macros from the `log` crate.
type CompatibilityCheck = fn((i32, i32, i32));

/// Configuration for a [`SMTSolverBuilder`]
#[derive(Debug, Clone)]
#[cfg_attr(feature = "config_deserialize", derive(Deserialize))]
pub struct SMTSolverBuilderCfg {
    /// Command to start the SMT solver
    command: String,
    /// Arguments to pass to the SMT solver command
    #[cfg_attr(feature = "config_deserialize", serde(default))]
    args: Vec<String>,
    /// Options to configure in the SMT solver
    #[cfg_attr(feature = "config_deserialize", serde(default))]
    opts: Vec<SMTSolverOption>,
    /// Sets the logic explicitly to `LIA`
    #[cfg_attr(feature = "config_deserialize", serde(default = "default_set_lia"))]
    set_lia: bool,
    /// Function to check version compatibility of the SMT solver
    #[cfg_attr(feature = "config_deserialize", serde(skip))]
    check_version: Option<CompatibilityCheck>,
}

impl PartialEq for SMTSolverBuilderCfg {
    /// Ignore the concrete function behind check version
    fn eq(&self, other: &Self) -> bool {
        self.command == other.command
            && self.args == other.args
            && self.opts == other.opts
            && self.set_lia == other.set_lia
            && self.check_version.is_some() == other.check_version.is_some()
    }
}

/// Function to get the default value for the `set_lia` field
#[cfg(feature = "config_deserialize")]
fn default_set_lia() -> bool {
    false
}

impl SMTSolverBuilderCfg {
    /// Create a new SMT solver builder configuration
    ///
    /// This function takes the command to start the SMT solver, the arguments
    /// to pass to the SMT solver, and the options to pass to the SMT solver.
    ///
    /// Additionally, it takes a boolean value to set the logic explicitly to
    /// linear integer arithmetic (LIA).
    ///
    /// Note that the SMT solver must be started in interactive
    /// REPL mode and accept input in the
    /// [SMT-LIB2](https://smtlib.cs.uiowa.edu) format.
    pub fn new(
        command: String,
        args: Vec<String>,
        opts: Vec<SMTSolverOption>,
        set_lia: bool,
    ) -> Self {
        Self {
            command,
            args,
            opts,
            set_lia,
            check_version: None,
        }
    }

    /// Get the default configuration for the Z3 SMT solver
    pub fn new_z3() -> Self {
        let opts = Vec::new();

        Self {
            command: Z3_PRG.to_string(),
            args: Z3_ARGS.iter().map(|s| s.to_string()).collect(),
            opts,
            set_lia: true,
            check_version: None,
        }
    }

    /// Get the default configuration for the CVC5 SMT solver
    pub fn new_cvc5() -> Self {
        let check_version = |version: (i32, i32, i32)| {
            if version.0 <= 1 && version.1 < 1 {
                warn!(
                    "Detected cvc5 < v1.1.0 (cvc5 is version {}.{}.{}). This version is not officially supported !",
                    version.0, version.1, version.2
                )
            }
        };

        Self {
            command: CVC5_PRG.to_string(),
            args: CVC5_ARGS.iter().map(|s| s.to_string()).collect(),
            opts: vec![],
            set_lia: true,
            check_version: Some(check_version),
        }
    }
}

/// Error that can occur when creating a new [`SMTSolverBuilder`]
#[derive(Debug, PartialEq, Clone)]
pub enum SMTSolverBuilderError {
    /// The SMT solver seems to not be installed
    NotInstalled(String),
}

impl fmt::Display for SMTSolverBuilderError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SMTSolverBuilderError::NotInstalled(s) => {
                write!(f, "SMT solver {s} is not installed")
            }
        }
    }
}

impl error::Error for SMTSolverBuilderError {}

/// Trait for types that can provide an [`SMTSolverBuilderCfg`]
pub trait ProvidesSMTSolverBuilderCfg {
    /// Get the [`SMTSolverBuilderCfg`]
    fn get_smt_solver_builder_cfg(&self) -> &SMTSolverBuilderCfg;
}

impl ProvidesSMTSolverBuilderCfg for SMTSolverBuilderCfg {
    fn get_smt_solver_builder_cfg(&self) -> &SMTSolverBuilderCfg {
        self
    }
}

/// Builder to create new [`SMTSolver`] instances
///
/// This builder can be used to create new SMT solver instances. Each new
/// instance will be using a separate solver process.
#[derive(Debug, Clone, PartialEq)]
pub struct SMTSolverBuilder {
    command: String,
    args: Vec<String>,
    opts: Vec<SMTSolverOption>,
    set_lia: bool,
}

impl SMTSolverBuilder {
    /// Create a new [`SMTSolverBuilder`] with the given configuration
    pub fn new(cfg: &SMTSolverBuilderCfg) -> Result<Self, SMTSolverBuilderError> {
        let version = get_smt_solver_version(&cfg.command);
        match version {
            Ok(version) => {
                trace!(
                    "SMT solver {} version {}.{}.{} found",
                    cfg.command, version.0, version.1, version.2
                );

                if let Some(check_version) = cfg.check_version {
                    check_version(version);
                }
            }
            Err(e) => match e {
                GetVersionError::NotInstalled(_) => {
                    return Err(SMTSolverBuilderError::NotInstalled(cfg.command.clone()));
                }
                GetVersionError::ParseVersionError => {
                    warn!("Failed to parse version of SMT solver {}", cfg.command);
                }
            },
        }

        Ok(Self {
            command: cfg.command.clone(),
            args: cfg.args.clone(),
            opts: cfg.opts.clone(),
            set_lia: cfg.set_lia,
        })
    }

    /// Create a new [`SMTSolver`] instance
    pub fn new_solver(&self) -> SMTSolver {
        trace!("Creating new solver instance of {}", self.command);
        let mut builder = ContextBuilder::new();

        if !self.command.is_empty() {
            builder.solver(&self.command).solver_args(&self.args);
        }

        let mut solver = builder.build().unwrap_or_else(|_| {
            panic!(
                "Failed to start interactive session with SMT solver. Command: {}",
                self.command
            )
        });

        for opt in self.opts.iter() {
            debug!("Applying SMT solver option {opt}");
            opt.apply_option(&mut solver);
        }

        if self.set_lia {
            debug!("Setting SMT solver logic to quantifier free LIA");
            solver
                .set_logic("LIA")
                .expect("Failed to set logic `LIA` in the SMT solver.");
        }

        solver
    }

    /// Create a new [`SMTSolver`] instance with a replay file recoding all
    /// interactions with the SMT solver
    pub fn new_solver_with_replay<W>(&mut self, replay_file: W) -> SMTSolver
    where
        W: Write + 'static + Send,
    {
        trace!("Creating new solver instance of {}", self.command);
        let mut builder = ContextBuilder::new();
        builder.replay_file(Some(replay_file));
        builder.solver(&self.command).solver_args(&self.args);

        let mut solver = builder.build().unwrap_or_else(|_| {
            panic!(
                "Failed to start interactive session with SMT solver. Command: {}",
                self.command
            )
        });

        for opt in self.opts.iter() {
            opt.apply_option(&mut solver);
        }

        if self.set_lia {
            debug!("Setting SMT solver logic to LIA");
            solver
                .set_logic("LIA")
                .expect("Failed to set logic `LIA` in the SMT solver.");
        }

        solver
    }

    /// Builder to automatically select a supported SMT solver
    ///
    /// This builder will try to start the CVC5 solver first, and if that fails, it
    /// will try to start the Z3 solver. If both fail, it will panic.
    pub fn new_automatic_selection() -> Result<Self, SMTSolverBuilderError> {
        if let Ok(z3) = SMTSolverBuilder::new(&SMTSolverBuilderCfg::new_z3()) {
            Ok(z3)
        } else if let Ok(cvc5) = SMTSolverBuilder::new(&SMTSolverBuilderCfg::new_cvc5()) {
            Ok(cvc5)
        } else {
            Err(SMTSolverBuilderError::NotInstalled(
                "No supported SMT solver found".to_string(),
            ))
        }
    }
}

impl Default for SMTSolverBuilder {
    /// Create a new [`SMTSolverBuilder`] which will automatically try to select
    /// a supported SMT solver, if one is installed on the system.
    fn default() -> Self {
        SMTSolverBuilder::new_automatic_selection()
            .expect("Failed to create default SMT solver builder. No SMT solver found.")
    }
}

/// Trait for structures provide [`SMTSolverBuilder`]s
///
/// This trait should be implemented by any type that can supply a model checker
/// with a configured SMT solver builder. This is useful for model checking
/// contexts that hold additional configuration such as for example BDD library
/// configuration.
pub trait ProvidesSMTSolverBuilder {
    /// Get the configured [`SMTSolverBuilder`]
    fn get_solver_builder(&self) -> SMTSolverBuilder;
}

impl ProvidesSMTSolverBuilder for SMTSolverBuilder {
    fn get_solver_builder(&self) -> SMTSolverBuilder {
        self.clone()
    }
}

/// Type for options that can be supplied to an SMT solver
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "config_deserialize", derive(Deserialize))]
pub enum SMTSolverOption {
    /// Option with boolean value
    BooleanOption {
        /// Name of the option
        name: String,
        /// Value to set the option to
        value: bool,
    },
    /// Option with unsigned integer value
    UnsignedIntOption {
        /// Name of the option
        name: String,
        /// Value to set the option to
        value: u32,
    },
}

impl SMTSolverOption {
    /// Create a new boolean [`SMTSolverOption`]
    pub fn new_boolean_opt(name: String, value: bool) -> Self {
        Self::BooleanOption { name, value }
    }

    /// Create a new integer  [`SMTSolverOption`]
    pub fn new_integer_opt(name: String, value: u32) -> Self {
        Self::UnsignedIntOption { name, value }
    }

    /// Apply option to the SMT solver
    pub fn apply_option(&self, solver: &mut SMTSolver) {
        match self {
            SMTSolverOption::BooleanOption { name, value } => {
                trace!("Setting SMT solver option {name} to {value}");
                let value = if *value {
                    solver.true_()
                } else {
                    solver.false_()
                };

                let res = solver.set_option(name, value);

                if let Err(e) = res {
                    error!("Failed to set option {} in SMT solver ! Error: {}", name, e);
                }
            }
            SMTSolverOption::UnsignedIntOption { name, value } => {
                trace!("Setting SMT solver option {name} to {value}");
                let value = solver.numeral(*value);
                let res = solver.set_option(name, value);

                if let Err(e) = res {
                    error!("Failed to set option {} in SMT solver ! Error: {}", name, e);
                }
            }
        }
    }
}

impl fmt::Display for SMTSolverOption {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SMTSolverOption::BooleanOption { name, value } => write!(f, "{name} : {value}"),
            SMTSolverOption::UnsignedIntOption { name, value } => write!(f, "{name} : {value}"),
        }
    }
}

/// Trait indicating that the a type holds an [`SMTSolver`]
///
/// This trait should be implemented by any type that holds an SMT solver, i.e.
/// a [`easy_smt::Context`] object. Implementing this trait will enable the type
/// to encode SMT expressions and check their satisfiability using the SMT
/// solver.
pub trait SMTSolverContext {
    /// Get a mutable reference to the SMT solver associated with this context
    fn get_smt_solver_mut(&mut self) -> &mut SMTSolver;

    /// Get the SMT solver associated with this context
    fn get_smt_solver(&self) -> &SMTSolver;

    /// Check the satisfiability of the given [`SMTExpr`]
    fn assert_and_check_expr(&mut self, expr: SMTExpr) -> Result<SMTSolution, SMTSolverError> {
        self.get_smt_solver_mut().assert(expr)?;
        let res = self.get_smt_solver_mut().check()?;

        match res {
            easy_smt::Response::Sat => Ok(SMTSolution::SAT),
            easy_smt::Response::Unsat => Ok(SMTSolution::UNSAT),
            easy_smt::Response::Unknown => Err(SMTSolverError::SolverTimeout),
        }
    }
}

impl SMTSolverContext for SMTSolver {
    fn get_smt_solver_mut(&mut self) -> &mut SMTSolver {
        self
    }

    fn get_smt_solver(&self) -> &SMTSolver {
        self
    }
}

/// Result of an SMT query
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum SMTSolution {
    /// Query was unsatisfiable
    UNSAT,
    /// Query was satisfiable
    SAT,
}

impl SMTSolution {
    /// Convert the SMT solution to a boolean
    pub fn is_sat(&self) -> bool {
        match self {
            SMTSolution::SAT => true,
            SMTSolution::UNSAT => false,
        }
    }
}

impl fmt::Display for SMTSolution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SMTSolution::UNSAT => write!(f, "UNSAT"),
            SMTSolution::SAT => write!(f, "SAT"),
        }
    }
}

/// Error that can occur when constructing a new SMT solver builder
#[derive(Debug, PartialEq)]
enum GetVersionError {
    /// Solver does not seem to be installed
    NotInstalled(String),
    /// Failed to parse version out of output
    ParseVersionError,
}

impl fmt::Display for GetVersionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GetVersionError::NotInstalled(s) => write!(
                f,
                "Execution of `{s} --version`  failed. This most likely means that the requested SMT solver is not installed."
            ),
            GetVersionError::ParseVersionError => write!(
                f,
                "Failed to parse version out of the output of `<SMT-SOLVER-COMMAND> --version`"
            ),
        }
    }
}

impl error::Error for GetVersionError {}

/// Calls solver and attempts to parse the version of the SMT solver that is used
fn get_smt_solver_version(cmd: &str) -> Result<(i32, i32, i32), GetVersionError> {
    let out = Command::new(cmd).arg("--version").output();
    if out.is_err() {
        return Err(GetVersionError::NotInstalled(cmd.to_owned()));
    }
    let out = out.unwrap();
    if !out.status.success() {
        return Err(GetVersionError::NotInstalled(cmd.to_owned()));
    }

    let out_str =
        std::str::from_utf8(&out.stdout).map_err(|_| GetVersionError::ParseVersionError)?;
    parse_smt_solver_version(out_str)
}

/// This function attempts to parse the version number from the output of the
/// `--version` command.
///
/// The version is the first whitespace-separated token of the form "x.y.z".
/// Returns a `ParseVersionError` if no such token exists.
fn parse_smt_solver_version(version_output: &str) -> Result<(i32, i32, i32), GetVersionError> {
    for token in version_output.split_whitespace() {
        let parts: Vec<&str> = token.split('.').collect();
        if parts.len() == 3
            && let (Ok(major), Ok(minor), Ok(patch)) =
                (parts[0].parse(), parts[1].parse(), parts[2].parse())
        {
            return Ok((major, minor, patch));
        }
    }

    debug!("Failed to parse SMT solver version from output: {version_output}");
    Err(GetVersionError::ParseVersionError)
}

#[cfg(test)]
mod tests {
    use std::vec;

    use easy_smt::Response;

    use super::*;

    fn test_solver_interaction(solver: &mut SMTSolver) {
        let int_sort = solver.int_sort();
        let x = solver.declare_const("x", int_sort).unwrap();

        let constr = solver.and(
            solver.lte(x, solver.numeral(2)),
            solver.gt(x, solver.numeral(1)),
        );
        solver.assert(constr).unwrap();

        assert_eq!(solver.check().unwrap(), Response::Sat);

        let solution = solver.get_value(vec![x]).unwrap();
        assert_eq!(solution.len(), 1);
        assert_eq!(solution[0].0, x);
        assert_eq!(solver.get_u64(solution[0].1).unwrap(), 2);
    }

    // Note: CVC5 smaller than 1.1.0 does not play nice with negative solutions
    fn test_solver_supports_negative_solutions(solver: &mut SMTSolver) {
        let int_sort = solver.int_sort();
        let z = solver.declare_const("z", int_sort).unwrap();

        let constr = solver.and(
            solver.lte(z, solver.numeral(-1)),
            solver.gt(z, solver.numeral(-2)),
        );
        solver.assert(constr).unwrap();

        assert_eq!(solver.check().unwrap(), Response::Sat);

        let solution = solver.get_value(vec![z]).unwrap();
        assert_eq!(solution.len(), 1);
        assert_eq!(solution[0].0, z);
        assert_eq!(solver.get_i64(solution[0].1).unwrap(), -1);
    }

    #[test]
    fn test_z3_solver() {
        let builder = SMTSolverBuilder::new(&SMTSolverBuilderCfg::new_z3());
        assert!(builder.is_ok());
        let builder = builder.unwrap();

        let mut solver = builder.new_solver();
        test_solver_interaction(&mut solver);
        test_solver_supports_negative_solutions(&mut solver);
    }

    #[test]
    fn test_cvc5_solver() {
        let builder = SMTSolverBuilder::new(&SMTSolverBuilderCfg::new_cvc5());
        assert!(builder.is_ok());
        let builder = builder.unwrap();

        let mut solver = builder.new_solver();
        test_solver_interaction(&mut solver);
    }

    #[test]
    fn test_cvc5_parse_version_1() {
        let out = "\
This is cvc5 version 1.1.0 [git tag 1.1.0 branch HEAD]
compiled with GCC version 11.4.0
on Dec 21 2023 01:08:41

Copyright (c) 2009-2023 by the authors and their institutional
affiliations listed at https://cvc5.github.io/people.html

cvc5 is open-source and is covered by the BSD license (modified).

THIS SOFTWARE IS PROVIDED AS-IS, WITHOUT ANY WARRANTIES.
USE AT YOUR OWN RISK.

This version of cvc5 is linked against the following non-(L)GPL'ed
third party libraries.

  CaDiCaL - Simplified Satisfiability Solver
  See https://github.com/arminbiere/cadical for copyright information.

  Editline Library
  See https://thrysoee.dk/editline
  for copyright information.

  SymFPU - The Symbolic Floating Point Unit
  See https://github.com/martin-cs/symfpu/tree/CVC4 for copyright information.

This version of cvc5 is linked against the following third party
libraries covered by the LGPLv3 license.
See licenses/lgpl-3.0.txt for more information.

  GMP - Gnu Multi Precision Arithmetic Library
  See http://gmplib.org for copyright information.

  LibPoly polynomial library
  See https://github.com/SRI-CSL/libpoly for copyright and
  licensing information.

cvc5 is statically linked against these libraries. To recompile
this version of cvc5 with different versions of these libraries
follow the instructions on https://github.com/cvc5/cvc5/blob/main/INSTALL.md

See the file COPYING (distributed with the source code, and with
all binaries) for the full cvc5 copyright, licensing, and (lack of)
warranty information.
";

        let got = parse_smt_solver_version(out);
        assert_eq!(got, Ok((1, 1, 0)))
    }

    #[test]
    fn test_cvc5_parse_version_2() {
        let out = "\
This is cvc5 version 1.2.0
compiled with GCC version 14.2.1 20240912 (Red Hat 14.2.1-3)
on Sep 26 2024 00:00:00

Copyright (c) 2009-2023 by the authors and their institutional
affiliations listed at https://cvc5.github.io/people.html

This build of cvc5 uses GPLed libraries, and is thus covered by
the GNU General Public License (GPL) version 3.  Versions of cvc5
are available that are covered by the (modified) BSD license. If
you want to license cvc5 under this license, please configure cvc5
with the \"--no-gpl\" option before building from sources.

THIS SOFTWARE IS PROVIDED AS-IS, WITHOUT ANY WARRANTIES.
USE AT YOUR OWN RISK.

This version of cvc5 is linked against the following non-(L)GPL'ed
third party libraries.

  CaDiCaL - Simplified Satisfiability Solver
  See https://github.com/arminbiere/cadical for copyright information.

  CryptoMiniSat - An Advanced SAT Solver
  See https://github.com/msoos/cryptominisat for copyright information.

  Kissat - Simplified Satisfiability Solver
  See https://fmv.jku.at/kissat for copyright information.

  Editline Library
  See https://thrysoee.dk/editline
  for copyright information.

  SymFPU - The Symbolic Floating Point Unit
  See https://github.com/martin-cs/symfpu/tree/CVC4 for copyright information.

This version of cvc5 is linked against the following third party
libraries covered by the LGPLv3 license.
See licenses/lgpl-3.0.txt for more information.

  GMP - Gnu Multi Precision Arithmetic Library
  See http://gmplib.org for copyright information.

  LibPoly polynomial library
  See https://github.com/SRI-CSL/libpoly for copyright and
  licensing information.

This version of cvc5 is linked against the following third party
libraries covered by the GPLv3 license.
See licenses/gpl-3.0.txt for more information.

  CoCoALib - a computer algebra library
  See https://cocoa.dima.unige.it/cocoa/cocoalib/index.shtml for copyright information

See the file COPYING (distributed with the source code, and with
all binaries) for the full cvc5 copyright, licensing, and (lack of)
warranty information.
";

        let got = parse_smt_solver_version(out);
        assert_eq!(got, Ok((1, 2, 0)))
    }

    #[test]
    fn test_cvc5_parse_version_3() {
        let out = "\
Could not read history from /root/.cvc5_history_smtlib2: No such file or directory
cvc5 1.4.0 [git b432cd7 on branch HEAD]
compiled as a unrestricted build with GCC version 11.4.0 on Sep 17 2026 21:14:31

Copyright (c) 2009-2026 by the authors and their institutional
affiliations listed at https://cvc5.github.io/people.html

cvc5 is open-source and is covered by the BSD license (modified).

THIS SOFTWARE IS PROVIDED AS-IS, WITHOUT ANY WARRANTIES.
USE AT YOUR OWN RISK.

This version of cvc5 is linked against the following non-(L)GPL'ed
third party libraries.

  CaDiCaL - Simplified Satisfiability Solver
  See https://github.com/arminbiere/cadical for copyright information.

  Editline Library
  See https://thrysoee.dk/editline
  for copyright information.

  SymFPU - The Symbolic Floating Point Unit
  See https://github.com/martin-cs/symfpu/tree/main for copyright information.

This version of cvc5 is linked against the following third party
libraries covered by the LGPLv3 license.
See licenses/lgpl-3.0.txt for more information.

  GMP - Gnu Multi Precision Arithmetic Library
  See http://gmplib.org for copyright information.

  LibPoly polynomial library
  See https://github.com/SRI-CSL/libpoly for copyright and
  licensing information.

cvc5 is statically linked against these libraries. To recompile
this version of cvc5 with different versions of these libraries
follow the instructions on https://github.com/cvc5/cvc5/blob/main/INSTALL.md

See the file COPYING (distributed with the source code, and with
all binaries) for the full cvc5 copyright, licensing, and (lack of)
warranty information.
";

        let got = parse_smt_solver_version(out);
        assert_eq!(got, Ok((1, 4, 0)))
    }

    #[test]
    fn test_z3_parse_version() {
        let out = "\
Z3 version 4.8.12 - 64 bit";

        let got = parse_smt_solver_version(out);
        assert_eq!(got, Ok((4, 8, 12)))
    }

    #[test]
    fn test_z3_get_version() {
        let version = get_smt_solver_version(Z3_PRG);
        assert!(version.is_ok());
    }

    #[test]
    fn test_cvc5_get_version() {
        let version = get_smt_solver_version(CVC5_PRG);
        assert!(version.is_ok());
    }

    #[test]
    fn test_automatic_solver_selection() {
        let builder = SMTSolverBuilder::new_automatic_selection()
            .expect("Failed to create default SMT solver builder. No SMT solver found.");

        let mut solver = builder.new_solver();
        test_solver_interaction(&mut solver);
    }

    #[test]
    fn test_command_solver() {
        let cvc5_args: Vec<String> = CVC5_ARGS.iter().map(|&s| s.to_string()).collect();

        let cfg = SMTSolverBuilderCfg::new("cvc5".to_string(), cvc5_args.clone(), vec![], false);
        let builder = SMTSolverBuilder::new(&cfg).unwrap();

        let mut solver = builder.new_solver();
        test_solver_interaction(&mut solver);

        let second_builder = builder.clone();
        assert_eq!(builder, second_builder);
    }

    #[test]
    fn test_command_solver_set_lia() {
        let cvc5_args: Vec<String> = CVC5_ARGS.iter().map(|&s| s.to_string()).collect();

        let cfg = SMTSolverBuilderCfg::new("cvc5".to_string(), cvc5_args.clone(), vec![], true);
        let builder = SMTSolverBuilder::new(&cfg).unwrap();

        let mut solver = builder.new_solver();
        test_solver_interaction(&mut solver);

        let second_builder = builder.clone();
        assert_eq!(builder, second_builder);
    }

    #[test]
    #[should_panic]
    fn test_panic_unknown_solver() {
        let cfg = SMTSolverBuilderCfg::new("unknown_solver".to_string(), vec![], vec![], false);
        let _builder = SMTSolverBuilder::new(&cfg).unwrap();
    }

    #[test]
    fn display_solution() {
        assert_eq!(SMTSolution::UNSAT.to_string(), "UNSAT");
        assert_eq!(SMTSolution::SAT.to_string(), "SAT");
    }

    #[test]
    fn test_is_sat() {
        assert!(!SMTSolution::UNSAT.is_sat());
        assert!(SMTSolution::SAT.is_sat());
    }

    #[test]
    fn test_get_version_error_display() {
        let err = GetVersionError::NotInstalled("cvc5".to_string());
        assert_eq!(
            err.to_string(),
            "Execution of `cvc5 --version`  failed. This most likely means that the requested SMT solver is not installed."
        );
        let err = GetVersionError::ParseVersionError;
        assert_eq!(
            err.to_string(),
            "Failed to parse version out of the output of `<SMT-SOLVER-COMMAND> --version`"
        );
        let err = GetVersionError::ParseVersionError;
        assert_eq!(
            err.to_string(),
            "Failed to parse version out of the output of `<SMT-SOLVER-COMMAND> --version`"
        );
    }

    #[test]
    fn test_solver_option_display() {
        let opt = SMTSolverOption::BooleanOption {
            name: ":opt".to_string(),
            value: true,
        };
        assert_eq!(opt.to_string(), ":opt : true");
        let opt = SMTSolverOption::UnsignedIntOption {
            name: ":opt".to_string(),
            value: 42,
        };
        assert_eq!(opt.to_string(), ":opt : 42");
    }

    #[test]
    fn test_new_solver_opt() {
        let opt = SMTSolverOption::new_boolean_opt(":opt".to_string(), true);
        assert_eq!(
            opt,
            SMTSolverOption::BooleanOption {
                name: ":opt".to_string(),
                value: true,
            }
        );
        let opt = SMTSolverOption::new_integer_opt(":opt".to_string(), 42);
        assert_eq!(
            opt,
            SMTSolverOption::UnsignedIntOption {
                name: ":opt".to_string(),
                value: 42,
            }
        );
    }

    #[test]
    fn test_fmt_solver_builder_error() {
        let err = SMTSolverBuilderError::NotInstalled("cvc5".to_string());
        assert_eq!(err.to_string(), "SMT solver cvc5 is not installed");
    }

    #[test]
    fn test_eq_smt_solver_builder_cfg() {
        let cfg1 = SMTSolverBuilderCfg::new(
            "cvc5".to_string(),
            vec!["--quiet".to_string(), "--lang=smt2".to_string()],
            vec![],
            false,
        );
        let cfg2 = SMTSolverBuilderCfg::new(
            "cvc5".to_string(),
            vec!["--quiet".to_string(), "--lang=smt2".to_string()],
            vec![],
            false,
        );
        assert_eq!(cfg1, cfg2);

        let cfg3 = SMTSolverBuilderCfg::new(
            "z3".to_string(),
            vec!["-smt2".to_string(), "-in".to_string(), "-v:0".to_string()],
            vec![],
            false,
        );
        assert_ne!(cfg1, cfg3);
    }
}
