//! This module tests some selected red belly benchmarks with resets

#[cfg(test)]
mod test_reset_benchmarks {
    use std::fs;

    use log::warn;
    use taco_acs_model_checker::{
        acs_threshold_automaton::ACSThresholdAutomaton, error_graph::ErrorGraph,
    };
    use taco_interval_ta::builder::IntervalTABuilder;
    use taco_model_checker::{
        TASpecification,
        internal_spec::{ErrorSpec, ErrorTarget},
    };
    use taco_parser::{ParseTAWithLTL, bymc::ByMCParser};
    use taco_smt_encoder::SMTSolverBuilder;
    use taco_threshold_automaton::lia_threshold_automaton::LIAThresholdAutomaton;

    const RESET_BENCHMARK_FOLDER: &str = "../../benchmarks/reset-benchmarks";

    #[test]
    fn test_srb() {
        let file = RESET_BENCHMARK_FOLDER.to_string() + "/SRB.eta";
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
                    let res = error_graph.check_for_non_spurious_counter_example(
                        SMTSolverBuilder::default().new_solver(),
                    );

                    assert!(res.is_safe(), "rb-RelBrd_V1.eta reported unsafe");
                }
            }
        }
    }

    #[test]
    fn test_rb_relbrd_v1() {
        let file = RESET_BENCHMARK_FOLDER.to_string() + "/rb-RelBrd_V1.eta";
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
                    let res = error_graph.check_for_non_spurious_counter_example(
                        SMTSolverBuilder::default().new_solver(),
                    );

                    assert!(res.is_safe(), "rb-RelBrd_V1.eta reported unsafe");
                }
            }
        }
    }
}
