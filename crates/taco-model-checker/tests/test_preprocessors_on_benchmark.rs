//! Integration tests the preprocessing of a threshold automaton.
use taco_parser::bymc::ByMCParser;
use taco_parser::*;

#[cfg(test)]
mod test_preprocessing {
    use std::{collections::HashSet, env, fs};

    use taco_model_checker::{
        ModelCheckerContext, TASpecification,
        internal_spec::ErrorSpec,
        preprocessing::{
            CollapseLocations, DropSelfLoops, DropUnreachableLocations, DropUnsatisfiableRules,
            Preprocessor, RemoveUnusedVariables, ReplaceTrivialGuardsSMT,
            ReplaceTrivialGuardsStatic,
        },
    };
    use taco_parser::ParseTAWithLTL;
    use taco_smt_encoder::SMTSolverBuilder;
    use taco_threshold_automaton::{ThresholdAutomaton, expressions::Location};
    use walkdir::WalkDir;

    use super::{ByMCParser, ParseTA};

    const BYMC_BENCHMARK_FOLDER: &str = "../../benchmarks/TACO";

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

    impl std::fmt::Display for DummySpec {
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

    /// This test will try to find all `.ta` recursively in the
    /// `BYMC_BENCHMARK_FOLDER` folder and will preprocess them using the
    /// `DropSelfLoops` preprocessor.
    #[test]
    fn test_all_drop_self_loops() {
        println!("Start {}", env::current_dir().unwrap().display());

        for entry in WalkDir::new(BYMC_BENCHMARK_FOLDER)
            .follow_links(true)
            .into_iter()
            .filter_map(|e| e.ok())
        {
            let f_name = entry.file_name().to_string_lossy();
            println!("Found file or folder {}", entry.path().to_string_lossy());

            if f_name.ends_with(".ta") {
                println!("Checking file {f_name}");

                let ta_str = fs::read_to_string(entry.path()).unwrap_or_else(|err| {
                    panic!(
                        "Failed to read file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                let parser = ByMCParser {};
                let mut ta = parser.parse_ta(&ta_str).unwrap_or_else(|err| {
                    panic!(
                        "Failed to parse file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                println!("Parsed successfully");

                let n_rules = ta.rules().count();

                println!("Preprocessing TA with DropSelfLoops");
                DropSelfLoops::new().process(&mut ta, &DummySpec::new(), &DummyContext {});

                println!(
                    "Preprocessing was successful. Removed {} rules",
                    n_rules - ta.rules().count()
                );
            }
        }

        println!("\nSuccessfully processed all benchmarks using DropSelfLoops!");
    }

    /// This test will try to find all `.ta` recursively in the
    /// `BYMC_BENCHMARK_FOLDER` folder and will try to process them using the
    /// `DropUnreachableLocations` preprocessor.
    #[test]
    fn test_all_drop_unreachable_locations() {
        println!("Start {}", env::current_dir().unwrap().display());

        for entry in WalkDir::new(BYMC_BENCHMARK_FOLDER)
            .follow_links(true)
            .into_iter()
            .filter_map(|e| e.ok())
        {
            let f_name = entry.file_name().to_string_lossy();
            println!("Found file or folder {}", entry.path().to_string_lossy());

            if f_name.ends_with(".ta") {
                println!("Checking file {f_name}");

                let ta_str = fs::read_to_string(entry.path()).unwrap_or_else(|err| {
                    panic!(
                        "Failed to read file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                let parser = ByMCParser {};
                let mut ta = parser.parse_ta(&ta_str).unwrap_or_else(|err| {
                    panic!(
                        "Failed to parse file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                println!("Parsed successfully");

                let n_rules = ta.rules().count();
                let n_locs = ta.locations().count();

                println!("Preprocessing TA with DropUnreachableLocation");
                DropUnreachableLocations::new().process(
                    &mut ta,
                    &DummySpec::new(),
                    &DummyContext {},
                );
                println!(
                    "Preprocessing was successful. Removed {} rules and {} locations",
                    n_rules - ta.rules().count(),
                    n_locs - ta.locations().count()
                );
            }
        }

        println!("\nSuccessfully processed all benchmarks using DropUnreachableLocation!");
    }

    /// This test will try to find all `.ta` recursively in the
    /// `BYMC_BENCHMARK_FOLDER` folder and will try to process them using the
    /// `DropUnreachableLocations` preprocessor.
    #[test]
    fn test_replace_trivial_guards_static() {
        println!("Start {}", env::current_dir().unwrap().display());

        for entry in WalkDir::new(BYMC_BENCHMARK_FOLDER)
            .follow_links(true)
            .into_iter()
            .filter_map(|e| e.ok())
        {
            let f_name = entry.file_name().to_string_lossy();
            println!("Found file or folder {}", entry.path().to_string_lossy());

            if f_name.ends_with(".ta") {
                println!("Checking file {f_name}");

                let ta_str = fs::read_to_string(entry.path()).unwrap_or_else(|err| {
                    panic!(
                        "Failed to read file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                let parser = ByMCParser {};
                let mut ta = parser.parse_ta(&ta_str).unwrap_or_else(|err| {
                    panic!(
                        "Failed to parse file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                println!("Parsed successfully");
                ReplaceTrivialGuardsStatic::new().process(
                    &mut ta,
                    &DummySpec::new(),
                    &DummyContext {},
                );
                println!("Preprocessing was successful");
            }
        }

        println!("\nSuccessfully processed all benchmarks using ReplaceTrivialGuardsStatic!");
    }

    /// This test will try to find all `.ta` recursively in the
    /// `BYMC_BENCHMARK_FOLDER` folder and will try to process them using the
    /// `DropUnreachableLocations` preprocessor.
    #[test]
    fn test_replace_trivial_guards_smt() {
        println!("Start {}", env::current_dir().unwrap().display());

        for entry in WalkDir::new(BYMC_BENCHMARK_FOLDER)
            .follow_links(true)
            .into_iter()
            .filter_map(|e| e.ok())
        {
            let f_name = entry.file_name().to_string_lossy();
            println!("Found file or folder {}", entry.path().to_string_lossy());

            if f_name.ends_with(".ta") {
                println!("Checking file {f_name}");

                let ta_str = fs::read_to_string(entry.path()).unwrap_or_else(|err| {
                    panic!(
                        "Failed to read file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                let parser = ByMCParser {};
                let mut ta = parser.parse_ta(&ta_str).unwrap_or_else(|err| {
                    panic!(
                        "Failed to parse file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                println!("Parsed successfully");

                ReplaceTrivialGuardsSMT::new().process(
                    &mut ta,
                    &DummySpec::new(),
                    &SMTSolverBuilder::default(),
                );
                println!("Preprocessing was successful");
            }
        }

        println!("\nSuccessfully processed all benchmarks using ReplaceTrivialGuardsSMT!");
    }

    /// This test will try to find all `.ta` recursively in the
    /// `BYMC_BENCHMARK_FOLDER` folder and will try to process them using the
    /// `DropUnreachableLocations` preprocessor.
    #[test]
    fn test_all_remove_unused_variables() {
        println!("Start {}", env::current_dir().unwrap().display());

        for entry in WalkDir::new(BYMC_BENCHMARK_FOLDER)
            .follow_links(true)
            .into_iter()
            .filter_map(|e| e.ok())
        {
            let f_name = entry.file_name().to_string_lossy();
            println!("Found file or folder {}", entry.path().to_string_lossy());

            if f_name.ends_with(".ta") {
                println!("Checking file {f_name}");

                let ta_str = fs::read_to_string(entry.path()).unwrap_or_else(|err| {
                    panic!(
                        "Failed to read file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                let parser = ByMCParser {};
                let mut ta = parser.parse_ta(&ta_str).unwrap_or_else(|err| {
                    panic!(
                        "Failed to parse file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                println!("Parsed successfully");

                let n_variables = ta.variables().count();

                println!("Preprocessing TA with RemoveUnusedVariables");
                RemoveUnusedVariables::new().process(&mut ta, &DummySpec::new(), &DummyContext {});
                println!(
                    "Preprocessing was successful. Removed {} variables",
                    n_variables - ta.variables().count()
                );
            }
        }

        println!("\nSuccessfully processed all benchmarks using RemoveUnusedVariables!");
    }

    #[test]
    fn test_all_remove_unsatisfiable_guard() {
        println!("Start {}", env::current_dir().unwrap().display());

        for entry in WalkDir::new(BYMC_BENCHMARK_FOLDER)
            .follow_links(true)
            .into_iter()
            .filter_map(|e| e.ok())
        {
            let f_name = entry.file_name().to_string_lossy();
            println!("Found file or folder {}", entry.path().to_string_lossy());

            if f_name.ends_with(".ta") {
                println!("Checking file {f_name}");

                let ta_str = fs::read_to_string(entry.path()).unwrap_or_else(|err| {
                    panic!(
                        "Failed to read file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                let parser = ByMCParser {};
                let mut ta = parser.parse_ta(&ta_str).unwrap_or_else(|err| {
                    panic!(
                        "Failed to parse file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                println!("Parsed successfully");

                DropUnsatisfiableRules::new().process(
                    &mut ta,
                    &DummySpec::new(),
                    &SMTSolverBuilder::default(),
                );
                println!("Preprocessing was successful.");
            }
        }

        println!("\nSuccessfully processed all benchmarks using DropUnsatisfiableGuards!");
    }

    /// This test will try to find all `.ta` recursively in the
    /// `BYMC_BENCHMARK_FOLDER` folder and will preprocess them using the
    /// `CollapseLocations` preprocessor.
    #[test]
    fn test_all_collapsable_locations() {
        println!("Start {}", env::current_dir().unwrap().display());

        // take a limited subset as the preprocessing is quite heavy
        for entry in WalkDir::new("../../benchmarks/TACO/isola18/ta-(handcoded)")
            .follow_links(true)
            .into_iter()
            .filter_map(|e| e.ok())
        {
            let f_name = entry.file_name().to_string_lossy();
            println!("Found file or folder {}", entry.path().to_string_lossy());

            if f_name.ends_with(".ta") {
                println!("Checking file {f_name}");

                let ta_str = fs::read_to_string(entry.path()).unwrap_or_else(|err| {
                    panic!(
                        "Failed to read file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                let parser = ByMCParser {};
                let (ta, spec) = parser.parse_ta_and_spec(&ta_str).unwrap_or_else(|err| {
                    panic!(
                        "Failed to parse file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                println!("Parsed successfully");

                println!("Preprocessing TA with CollapseLocations");

                let spec = spec.expressions();
                let properties = spec.iter().map(|(name, eltlexpression)| {
                    ErrorSpec::from_named_eltl(name, eltlexpression.clone())
                });

                for property in properties {
                    match property {
                        Ok(prop) => {
                            let tas = prop.create_tas_to_check(&ta);
                            for (target, mut ta) in tas {
                                let n_locations = ta.locations().count();
                                let n_rules = ta.rules().count();
                                CollapseLocations::new().process(&mut ta, &target, &DummyContext);
                                println!(
                                    "Preprocessing for specification {} was successful. Removed {} locations and {} rules.",
                                    prop.name(),
                                    n_locations - ta.locations().count(),
                                    n_rules - ta.rules().count(),
                                );
                            }
                        }
                        Err(err) => {
                            println!("Property could not be preprocessed: {err}.")
                        }
                    }
                }
            }
        }

        println!("\nSuccessfully processed all benchmarks using CollapseLocations!");
    }
}
