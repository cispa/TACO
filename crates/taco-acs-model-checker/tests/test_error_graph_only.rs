//! These tests do only test the error graph construction, but do not check
//! potential error paths for non-spurious paths

#[cfg(test)]
mod test_error_graph_construction_only {
    use std::{env, fs, time::Instant};

    use log::warn;
    use taco_acs_model_checker::{
        acs_threshold_automaton::ACSThresholdAutomaton, error_graph::ErrorGraph,
    };
    use taco_interval_ta::{IntervalThresholdAutomaton, builder::IntervalTABuilder};

    use taco_model_checker::{
        SpecificationTrait, TASpecification, TATrait,
        internal_spec::{ErrorSpec, ErrorTarget},
        preprocessing::{
            self, DropSelfLoops, DropUnreachableLocations, RemoveUnusedVariables,
            ReplaceTrivialGuardsSMT,
        },
    };
    use taco_parser::{ParseTAWithLTL, bymc::ByMCParser};
    use taco_smt_encoder::{SMTSolverBuilder, SMTSolverBuilderCfg};
    use taco_threshold_automaton::lia_threshold_automaton::LIAThresholdAutomaton;
    use walkdir::WalkDir;

    const BYMC_BENCHMARK_FOLDER: &str = "../../benchmarks/TACO/isola18/ta-(handcoded)";

    #[test]
    fn test_error_graph_can_be_built_for_small_benchmarks() {
        println!("Start {}", env::current_dir().unwrap().display());

        for entry in WalkDir::new(BYMC_BENCHMARK_FOLDER)
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
                ];
                let ctx = SMTSolverBuilder::new(&SMTSolverBuilderCfg::new_z3()).unwrap();

                let ta_spec = ErrorSpec::transform_threshold_automaton(ta, parsed_spec, &ctx);
                let ta_spec = ta_spec
                    .into_iter()
                    .map(|(_, spec, mut ta)| {
                        // Preprocessing on tas with information from the specification
                        for processor in preprocessors.iter() {
                            processor.process(&mut ta, &spec, &ctx);
                        }

                        let ta = IntervalThresholdAutomaton::try_from_general_ta(ta, &ctx, &spec)?;

                        Ok::<_, Box<dyn std::error::Error>>((spec, ta))
                    })
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap();

                for (spec, interval_tas) in ta_spec {
                    for ta in interval_tas {
                        let cs_ta = ACSThresholdAutomaton::new(ta);

                        let ErrorTarget::Reach(spec) = &spec else {
                            warn!("Skipping Liveness");
                            continue;
                        };

                        let _error_graph =
                            ErrorGraph::compute_error_graph(spec.clone(), cs_ta.clone());
                    }
                }

                let elapsed = now.elapsed();
                println!(
                    "Finished error graph construction {} in {}ms\n\n\n",
                    f_name,
                    elapsed.as_millis()
                )
            }
        }

        println!("\nSuccessfully checked all benchmarks !");
    }

    #[test]
    fn test_aba_err_graph_empty() {
        let file = BYMC_BENCHMARK_FOLDER.to_string() + "/aba.ta";
        let ta_str = fs::read_to_string(file.clone())
            .unwrap_or_else(|err| panic!("Failed to read file {}: {}", file, err));

        let parser = ByMCParser {};
        let (ta, ltl) = parser
            .parse_ta_and_spec(&ta_str)
            .unwrap_or_else(|err| panic!("Failed to parse file {}: {}", file, err));

        let parsed_spec = ltl
            .expressions()
            .iter()
            .flat_map(|(n, s)| ErrorSpec::from_named_eltl(n.clone(), s.clone()))
            .collect::<Vec<_>>();

        let ta_spec = parsed_spec
            .into_iter()
            .flat_map(|spec| {
                let res: Vec<_> = spec
                    .create_tas_to_check(&ta)
                    .map(|(spec, ta)| (spec, vec![ta]))
                    .collect();
                res
            })
            .collect::<Vec<_>>();

        for (spec, tas) in ta_spec {
            for ta in tas {
                let lia_ta = LIAThresholdAutomaton::try_from(ta).unwrap();
                let interval_tas = IntervalTABuilder::new(
                    lia_ta,
                    SMTSolverBuilder::default(),
                    spec.var_constraint().into_iter().cloned().collect(),
                )
                .build()
                .unwrap();
                for ta in interval_tas {
                    let cs_ta = ACSThresholdAutomaton::new(ta);

                    let ErrorTarget::Reach(spec) = &spec else {
                        warn!("Skipping Liveness");
                        continue;
                    };

                    let error_graph = ErrorGraph::compute_error_graph(spec.clone(), cs_ta);
                    assert!(
                        error_graph.is_empty(),
                        "aba error graph was found to be non empty!"
                    );
                }
            }
        }
    }

    #[test]
    fn test_strb_err_graph_empty() {
        let file = BYMC_BENCHMARK_FOLDER.to_string() + "/strb.ta";
        let ta_str = fs::read_to_string(file.clone())
            .unwrap_or_else(|err| panic!("Failed to read file {}: {}", file, err));

        let parser = ByMCParser {};
        let (ta, ltl) = parser
            .parse_ta_and_spec(&ta_str)
            .unwrap_or_else(|err| panic!("Failed to parse file {}: {}", file, err));

        let parsed_spec = ltl
            .expressions()
            .iter()
            .flat_map(|(n, s)| ErrorSpec::from_named_eltl(n.clone(), s.clone()))
            .collect::<Vec<_>>();

        let ta_spec = parsed_spec
            .into_iter()
            .flat_map(|spec| {
                let res: Vec<_> = spec
                    .create_tas_to_check(&ta)
                    .map(|(spec, ta)| (spec, vec![ta]))
                    .collect();
                res
            })
            .collect::<Vec<_>>();

        for (spec, tas) in ta_spec {
            for ta in tas {
                let lia_ta = LIAThresholdAutomaton::try_from(ta).unwrap();
                let interval_tas = IntervalTABuilder::new(
                    lia_ta,
                    SMTSolverBuilder::default(),
                    spec.var_constraint().into_iter().cloned().collect(),
                )
                .build()
                .unwrap();
                for ta in interval_tas {
                    let cs_ta = ACSThresholdAutomaton::new(ta);

                    let org_tgt = &spec;
                    let ErrorTarget::Reach(spec) = &spec else {
                        warn!("Skipping Liveness");
                        continue;
                    };

                    let error_graph = ErrorGraph::compute_error_graph(spec.clone(), cs_ta);
                    assert!(
                        error_graph.is_empty(),
                        "strb error graph for spec '{org_tgt}' was found to be non empty!"
                    );
                }
            }
        }
    }

    #[test]
    fn test_bcrb_err_graph_empty() {
        let file = BYMC_BENCHMARK_FOLDER.to_string() + "/bcrb.ta";
        let ta_str = fs::read_to_string(file.clone())
            .unwrap_or_else(|err| panic!("Failed to read file {}: {}", file, err));

        let parser = ByMCParser {};
        let (ta, ltl) = parser
            .parse_ta_and_spec(&ta_str)
            .unwrap_or_else(|err| panic!("Failed to parse file {}: {}", file, err));

        let parsed_spec = ltl
            .expressions()
            .iter()
            .flat_map(|(n, s)| ErrorSpec::from_named_eltl(n.clone(), s.clone()))
            .collect::<Vec<_>>();

        let ta_spec = parsed_spec
            .into_iter()
            .flat_map(|spec| {
                let res: Vec<_> = spec
                    .create_tas_to_check(&ta)
                    .map(|(spec, ta)| (spec, vec![ta]))
                    .collect();
                res
            })
            .collect::<Vec<_>>();

        for (spec, tas) in ta_spec {
            for ta in tas {
                let lia_ta = LIAThresholdAutomaton::try_from(ta).unwrap();
                let interval_tas = IntervalTABuilder::new(
                    lia_ta,
                    SMTSolverBuilder::default(),
                    spec.var_constraint().into_iter().cloned().collect(),
                )
                .build()
                .unwrap();
                for ta in interval_tas {
                    let cs_ta = ACSThresholdAutomaton::new(ta);

                    let ErrorTarget::Reach(spec) = &spec else {
                        warn!("Skipping Liveness");
                        continue;
                    };

                    let error_graph = ErrorGraph::compute_error_graph(spec.clone(), cs_ta);
                    assert!(
                        error_graph.is_empty(),
                        "bcrb error graph was found to be non empty!"
                    );
                }
            }
        }
    }
}
