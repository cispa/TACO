//! Integration tests the preprocessing of a threshold automaton.
use taco_parser::bymc::ByMCParser;

#[cfg(test)]
mod test_extract_spec_from_benchmarks {
    use std::{env, fs};

    use env_logger::Env;
    use taco_model_checker::{SpecificationTrait, internal_spec::ErrorSpec};
    use taco_parser::ParseTAWithLTL;
    use taco_smt_encoder::SMTSolverBuilder;

    use walkdir::WalkDir;

    use super::ByMCParser;

    const BYMC_BENCHMARK_FOLDER: &str = "../../benchmarks/TACO";

    /// This test will try to find all `.ta` recursively in the
    /// `BYMC_BENCHMARK_FOLDER` folder and will preprocess them using the
    /// `DropSelfLoops` preprocessor.
    #[test]
    fn test_extract_spec() {
        println!("Start {}", env::current_dir().unwrap().display());

        let env = Env::default()
            .filter_or("MY_LOG_LEVEL", "info")
            .write_style_or("MY_LOG_STYLE", "always");
        env_logger::init_from_env(env);

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
                let (_ta, ltl) = parser.parse_ta_and_spec(&ta_str).unwrap_or_else(|err| {
                    panic!(
                        "Failed to parse file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                println!("Parsed successfully");

                let ctx = SMTSolverBuilder::default();

                let (parsed_spec, _) = ErrorSpec::try_from_eltl(ltl.into_iter(), &ctx).unwrap();

                assert!(!parsed_spec.is_empty());

                println!("Parsed {} ltl expressions into spec", parsed_spec.len());
            }
        }

        println!("\nSuccessfully processed all benchmarks !");
    }
}
