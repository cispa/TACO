//! Integration tests the preprocessing of a threshold automaton.

#[cfg(test)]
mod test_extract_spec_from_benchmarks {
    use std::time::Instant;
    use std::{env, fs};

    use taco_model_checker::internal_spec::{ErrorSpec, ErrorTarget};
    use taco_model_checker::preprocessing::{
        DropSelfLoops, DropUnreachableLocations, DropUnsatisfiableRules, RemoveUnusedVariables,
        ReplaceTrivialGuardsSMT,
    };

    use taco_model_checker::{ModelChecker, ModelCheckerResult, SpecificationTrait, preprocessing};

    use taco_parser::ParseTAWithLTL;

    use taco_model_checker::TATrait;
    use taco_parser::bymc::ByMCParser;
    use taco_smt_encoder::{SMTSolverBuilder, SMTSolverBuilderCfg};
    use taco_smt_model_checker::{SMTModelChecker, SMTModelCheckerOptions};
    use taco_threshold_automaton::general_threshold_automaton::GeneralThresholdAutomaton;
    use walkdir::WalkDir;

    const BYMC_BENCHMARK_FOLDER: &str = "../../benchmarks/TACO";
    const SMALL_BENCHMARKS_FOLDER: &str = "../../benchmarks/TACO/isola18/ta-(handcoded)";

    /// This test will try to find all `.ta` recursively in the
    /// `BYMC_BENCHMARK_FOLDER` folder and will try to check all of them using
    /// the **SMTModelChecker**
    #[test]
    #[cfg(feature = "parallel")]
    #[ignore = "long running test"]
    fn test_smt_model_checker_on_all_benchmarks() {
        println!("Start {}", env::current_dir().unwrap().display());

        for entry in WalkDir::new(BYMC_BENCHMARK_FOLDER)
            .follow_links(true)
            .into_iter()
            .filter_map(|e| e.ok())
        {
            let f_name = entry.file_name().to_string_lossy();
            println!("Found file or folder {}", entry.path().to_string_lossy());

            if f_name.ends_with(".ta") {
                use taco_model_checker::ModelChecker;
                use taco_smt_model_checker::SMTModelCheckerOptions;

                let now = Instant::now();
                println!("Checking file {f_name}");

                let ta_str = fs::read_to_string(entry.path()).unwrap_or_else(|err| {
                    panic!(
                        "Failed to read file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                let parser = ByMCParser {};
                let (ta, ltl) = parser.parse_ta_and_spec(&ta_str).unwrap_or_else(|err| {
                    panic!(
                        "Failed to parse file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                println!("Parsed successfully");

                let parsed_spec = ltl
                    .expressions()
                    .iter()
                    .flat_map(|(n, s)| ErrorSpec::from_named_eltl(n.clone(), s.clone()))
                    .collect::<Vec<_>>();

                println!("Parsed {} ltl expressions into spec", parsed_spec.len());

                let preprocessors: Vec<Box<dyn preprocessing::Preprocessor<_, _, _>>> = vec![
                    Box::new(ReplaceTrivialGuardsSMT::new()),
                    Box::new(DropSelfLoops::new()),
                    Box::new(DropUnreachableLocations::new()),
                    Box::new(RemoveUnusedVariables::new()),
                    Box::new(DropUnsatisfiableRules::new()),
                ];
                let ctx = SMTSolverBuilder::default();

                let ta_spec = ErrorSpec::transform_threshold_automaton(ta, parsed_spec, &ctx);
                let ta_spec = ta_spec
                    .into_iter()
                    .map(|(name, spec, mut ta)| {
                        // Preprocessing on tas with information from the specification

                        for processor in preprocessors.iter() {
                            processor.process(&mut ta, &spec, &ctx);
                        }

                        let ta: Vec<GeneralThresholdAutomaton> =
                            GeneralThresholdAutomaton::try_from_general_ta(ta, &ctx, &())?;

                        Ok::<_, Box<dyn std::error::Error>>((name, spec, ta))
                    })
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap();

                let mc = SMTModelChecker::initialize(
                    SMTModelCheckerOptions::new_parallel(),
                    ta_spec,
                    Vec::new(),
                    SMTSolverBuilder::new(&SMTSolverBuilderCfg::new_z3()).unwrap(),
                )
                .expect("SMTModelChecker initialization failed");

                mc.verify(false)
                    .expect("Failed to verify threshold automaton");

                let elapsed = now.elapsed();
                println!(
                    "Finished checking ta {} in {}ms\n\n",
                    f_name,
                    elapsed.as_millis()
                )
            }
        }

        println!("\nSuccessfully processed all benchmarks !");
    }

    /// This test will try to find all `.ta` recursively in the
    /// `BYMC_BENCHMARK_FOLDER` folder and will try to check all of them using
    /// the **SMTModelChecker**
    ///
    /// This version of the tests will **not** go through the benchmarks in the
    /// subfolder! It is designed to run as a small integration test and should
    /// therefore only need a limited amount of time
    #[test]
    fn test_smt_model_checker_on_small_benchmarks() {
        println!("Start {}", env::current_dir().unwrap().display());

        for entry in WalkDir::new(SMALL_BENCHMARKS_FOLDER)
            .max_depth(1)
            .into_iter()
            .filter_map(|e| e.ok())
        {
            let f_name = entry.file_name().to_string_lossy();
            println!("Found file or folder {}", entry.path().to_string_lossy());

            if f_name.ends_with(".ta") {
                let now = Instant::now();
                println!("Checking file {f_name}");

                let ta_str = fs::read_to_string(entry.path()).unwrap_or_else(|err| {
                    panic!(
                        "Failed to read file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                let parser = ByMCParser {};
                let (ta, ltl) = parser.parse_ta_and_spec(&ta_str).unwrap_or_else(|err| {
                    panic!(
                        "Failed to parse file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                println!("Parsed successfully");

                let parsed_spec = ltl
                    .expressions()
                    .iter()
                    .flat_map(|(n, s)| ErrorSpec::from_named_eltl(n.clone(), s.clone()))
                    .collect::<Vec<_>>();

                println!("Parsed {} ltl expressions into spec", parsed_spec.len());

                let preprocessors: Vec<Box<dyn preprocessing::Preprocessor<_, _, _>>> = vec![
                    Box::new(ReplaceTrivialGuardsSMT::new()),
                    Box::new(DropSelfLoops::new()),
                    Box::new(DropUnreachableLocations::new()),
                    Box::new(RemoveUnusedVariables::new()),
                    Box::new(DropUnsatisfiableRules::new()),
                ];
                let ctx = SMTSolverBuilder::default();

                let ta_spec = ErrorSpec::transform_threshold_automaton(ta, parsed_spec, &ctx);
                let ta_spec = ta_spec
                    .into_iter()
                    .map(|(name, spec, mut ta)| {
                        // Preprocessing on tas with information from the specification

                        for processor in preprocessors.iter() {
                            processor.process(&mut ta, &spec, &ctx);
                        }

                        let ta = GeneralThresholdAutomaton::try_from_general_ta(ta, &ctx, &())?;

                        Ok::<_, Box<dyn std::error::Error>>((name, spec, ta))
                    })
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap();

                // Properties without reachability target (e.g. liveness) are
                // not supported by the SMT model checker
                let mut expected_unknown = ta_spec
                    .iter()
                    .filter(|(_, spec, _)| !matches!(spec, ErrorTarget::Reach(_)))
                    .map(|(name, _, _)| name.clone())
                    .collect::<Vec<_>>();
                expected_unknown.sort();
                expected_unknown.dedup();

                let mc = SMTModelChecker::initialize(
                    SMTModelCheckerOptions::default(),
                    ta_spec,
                    Vec::new(),
                    SMTSolverBuilder::new(&SMTSolverBuilderCfg::new_z3()).unwrap(),
                )
                .expect("SMTModelChecker initialization failed");

                let res = mc
                    .verify(false)
                    .expect("Failed to verify threshold automaton");

                if expected_unknown.is_empty() {
                    assert_eq!(res, ModelCheckerResult::SAFE);
                } else {
                    let ModelCheckerResult::UNKNOWN(mut unknown) = res else {
                        panic!("Expected UNKNOWN({expected_unknown:?}), got {res:?}");
                    };
                    unknown.sort();
                    unknown.dedup();
                    assert_eq!(unknown, expected_unknown);
                }

                let elapsed = now.elapsed();
                println!(
                    "Finished checking ta {} in {}ms\n\n\n",
                    f_name,
                    elapsed.as_millis()
                )
            }
        }

        println!("\nSuccessfully checked all benchmarks !");
    }

    /// This test will try to find all `.ta` recursively in the
    /// `BYMC_BENCHMARK_FOLDER` folder and will try to check all of them using
    /// the **SMTModelChecker**
    ///
    /// This version of the tests will **not** go through the benchmarks in the
    /// subfolder! It is designed to run as a small integration test and should
    /// therefore only need a limited amount of time
    #[test]
    #[cfg(feature = "parallel")]
    fn test_smt_model_checker_on_small_benchmarks_parallel() {
        // let env = Env::default()
        //     .filter_or("MY_LOG_LEVEL", "error")
        //     .write_style_or("MY_LOG_STYLE", "always");
        // env_logger::init_from_env(env);

        println!("Start {}", env::current_dir().unwrap().display());

        for entry in WalkDir::new(BYMC_BENCHMARK_FOLDER)
            .max_depth(1)
            .into_iter()
            .filter_map(|e| e.ok())
        {
            let f_name = entry.file_name().to_string_lossy();
            println!("Found file or folder {}", entry.path().to_string_lossy());

            if f_name.ends_with(".ta") {
                use taco_model_checker::{
                    SpecificationTrait,
                    preprocessing::{
                        self, DropSelfLoops, DropUnreachableLocations, DropUnsatisfiableRules,
                        RemoveUnusedVariables, ReplaceTrivialGuardsSMT,
                    },
                };

                let now = Instant::now();
                println!("Checking file {f_name}");

                let ta_str = fs::read_to_string(entry.path()).unwrap_or_else(|err| {
                    panic!(
                        "Failed to read file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                let parser = ByMCParser {};
                let (ta, ltl) = parser.parse_ta_and_spec(&ta_str).unwrap_or_else(|err| {
                    panic!(
                        "Failed to parse file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                println!("Parsed successfully");

                let parsed_spec = ltl
                    .expressions()
                    .iter()
                    .flat_map(|(n, s)| ErrorSpec::from_named_eltl(n.clone(), s.clone()))
                    .collect::<Vec<_>>();

                println!("Parsed {} ltl expressions into spec", parsed_spec.len());

                let preprocessors: Vec<Box<dyn preprocessing::Preprocessor<_, _, _>>> = vec![
                    Box::new(ReplaceTrivialGuardsSMT::new()),
                    Box::new(DropSelfLoops::new()),
                    Box::new(DropUnreachableLocations::new()),
                    Box::new(RemoveUnusedVariables::new()),
                    Box::new(DropUnsatisfiableRules::new()),
                ];
                let ctx = SMTSolverBuilder::default();

                let ta_spec = ErrorSpec::transform_threshold_automaton(ta, parsed_spec, &ctx);
                let ta_spec = ta_spec
                    .into_iter()
                    .map(|(name, spec, mut ta)| {
                        // Preprocessing on tas with information from the specification

                        for processor in preprocessors.iter() {
                            processor.process(&mut ta, &spec, &ctx);
                        }

                        let ta = GeneralThresholdAutomaton::try_from_general_ta(ta, &ctx, &())?;

                        Ok::<_, Box<dyn std::error::Error>>((name, spec, ta))
                    })
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap();

                let mc = SMTModelChecker::initialize(
                    SMTModelCheckerOptions::new_parallel(),
                    ta_spec,
                    Vec::new(),
                    SMTSolverBuilder::new(&SMTSolverBuilderCfg::new_z3()).unwrap(),
                )
                .expect("SMTModelChecker initialization failed");

                mc.verify(false)
                    .expect("Failed to verify threshold automaton");

                let elapsed = now.elapsed();
                println!(
                    "Finished checking ta {} in {}ms\n\n\n",
                    f_name,
                    elapsed.as_millis()
                )
            }
        }

        println!("\nSuccessfully checked all benchmarks !");
    }
}
