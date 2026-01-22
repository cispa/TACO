# Developer Documentation

**Welcome to the TACO Developer Documentation!**

<!--This page serves as the index page to the developer documentation -->

This is the developer documentation for the Threshold Automata for COnsensus
Model Checker (TACO), targeted towards users that want to modify TACO or
implement their own algorithms in TACO.
It consists of two main sections:

- [Crates](#crates) gives a high-level overview of the crates of TACO, and
- [Development Setup](#development-setup) contains setup instructions for a
  development environment for working on the TACO source code

(crates)=

## Crates

This section describes the high-level function of the crates that comprise the
TACO toolsuite. You can find the source code for all of them in the `crates`
directory.

:::{tip}
Clicking on the name of a crate will forward you to Rust documentation
of the crate, containing the API documentation as well as implementation
details.

Note that the documentation is also available on [docs.rs](https://docs.rs).
However, our internal version also contains the documentation for private types,
giving you more insights into the implementation details.
:::

### Threshold Automaton Representations

These crates define different representations of threshold automata at different
levels of abstraction, which can be used as inputs to model checkers.

- [`taco-interval-ta`](./taco_interval_ta/index.html):
  This library crate implements the interval abstraction of a threshold
  automaton. It contains a threshold automaton type that uses sets of
  (symbolic) intervals as guards.
- [`taco-threshold-automaton`](./taco_threshold_automaton/index.html): This crate defines
  the types:
  - `GeneralThresholdAutomaton`, which is the most general form of a threshold
    automaton. For example, it allows comparisons between variables or guards in
    non-linear arithmetic. This type is designed to be easily parsable from a
    specification file, while providing some basic validation (by using the
    `GeneralThresholdAutomatonBuilder`).
  - `LIAThresholdAutomaton`: A threshold automaton that is guaranteed to have
    only guards using integer linear arithmetic.

### Model Checker Crates

Model checkers and specifications must implement the interfaces defined in the

- [`taco-model-checker`](./taco_model_checker/index.html) crate. This library crate
  defines the common interface for model checkers, as well as some useful
  preprocessing tools that can apply useful transformations or simplifications
  to threshold automata.

TACO already implements 3 algorithms, which are split into their own separate
crates:

- [`taco-acs-model-checker`](./taco_acs_model_checker/index.html): Contains the
  implementation of the 'ACS' model checker.
- [`taco-smt-model-checker`](./taco_smt_model_checker/index.html): Contains the
  implementation of the 'SMT' model checker.
- [`taco-zcs-model-checker`](./taco_zcs_model_checker/index.html): Contains the
  implementation of the 'ZCS' model checker.

### Backend and Utility Crates

- [`taco-bdd`](./taco_bdd/index.html) : This library crate implements a common interface
  to interact with BDD libraries. Currently it supports
  [OxiDD](https://oxidd.net/) and [CUDD](https://github.com/cuddorg/cudd).
- [`taco-cli`](./taco_cli/index.html): The binary crate containing the code of
  the TACO Command Line Interface.
- [`taco-display-utils`](./taco_display_utils/index.html): A small library crate for
  common helper methods for nicely displaying types.
- [`taco-parser`](./taco_parser/index.html): An interface definition of parsers that can be
  used to parse a threshold automaton from different formats. This crate already
  contains a parser for `.ta` and `.eta` files that has been introduced by ByMC
  [here](https://github.com/konnov/bymc/blob/master/bymc/doc/ta-format.md).
- [`taco-smt-encoder`](./taco_smt_encoder/index.html): This library crate implements
  the configuration and setup of connections to SMT solvers. Additionally, it
  defines SMT encodings of types of the `threshold-automaton` crate and provides
  structures to encode constraints on configurations and paths.

(development-setup)=

## Development Setup

### Build TACO Executable

To build TACO you need the Rust tool chain to be installed. You can find
instructions for the installation on the
[official installation website](https://rust-lang.org/tools/install/).

Once you have Rust and Rust's package manager installed, you can build TACO by
executing:

```bash
# Build TACO
cargo build
# or: build taco in release mode (executable can be found under `./target/release`)
cargo build --release
```

Executing this command will build the `taco-cli` executable which you can find
in the directory `./target/debug`.

While cargo will take care of installing all packages that are required to build
TACO, to use TACO, at least one supported SMT solver must be installed. Please
note that to execute the unit and integration tests, you will need to have Z3
and/or CVC5 installed. You can find installation instructions for supported SMT
solvers [here](./taco-cli.md#supported-smt-solvers).

For installation instructions and additional components you might want to
install, you can refer to
[](./usage-cli/install.md#prerequisites).

### Executing Tests & Code Coverage

You can execute all tests in TACO by using

```bash
cargo test --all-targets --all-features
```

If you want to obtain a code coverage report locally, you will need to have

- llvm-tools, and
- [grcov](https://github.com/mozilla/grcov) installed

We have automated the installation and report generation in the
`coverage-report.sh` script, which you can execute using

```bash
./scripts/coverage-report.sh
```

#### Note: Integration Tests and Benchmark Files

This repo does contain integration tests that will automatically test TACO's
components against subsets of the benchmark files that are stored under
`benchmarks/TACO` and end with `.ta` or `.eta`. The purpose of these tests is to
ensure that our tool can cope with all the benchmarks we/others have come up
with.

When adding benchmarks, be careful, as they might impact the integration tests
and subsequently CI pipelines. If you want benchmark files to be excluded from
these tests, you can for example add the ending `*.ta-ignore`.

### Building the Developer Documentation

TACO uses the standard
[Rust Doc comment](https://doc.rust-lang.org/rust-by-example/meta/doc.html)
and adds this page as a custom landing page. To build the developer documentation
you can use the `generate-dev-docs.sh` script by executing:

```bash
./scripts/generate-dev-docs.sh
```

Or, you can also use the built-in cargo command:

```bash
cargo doc --open
```

However, this will not include the landing page of the documentation.

### Displaying & Editing the User Documentation

The user documentation files for TACO can be found in the `/docs`. We use
[MyST Markdown](https://mystmd.org/) for the TACO documentation.

To install MyST please refer to
[Installation Guide on the MyST website](https://mystmd.org/guide/installing)

Once MyST is installed, the documentation can be served by executing

```bash
# Start MyST in the `./docs` directory
cd ./docs && myst start
```

### Debugging

TACO uses the Rust [`log`](https://crates.io/crates/log) crate for logging.

You can enable debug output in TACO by using the `--debug` flag. If you want
even more detailed output, you can set the log level to trace, for example, by
setting the `RUST_LOG` environment variable using:

```bash
export RUST_LOG="trace"
```

### BDD Libraries

#### Building CUDD from Sources

Support for the [CUDD](https://github.com/cuddorg/cudd) library is added via the
[`cudd_sys`](https://docs.rs/cudd-sys/latest/cudd_sys/) package.

If you are having issues with building CUDD (though they should be fixed in
`1.1.0`), you can try building CUDD from sources. This will require:

- a C-compiler
- autoconf
- automake
- libtool

to be installed.

<details> <summary><b>CUDD Build Chain Installation</b></summary>

On Debian / Ubuntu you can use

```bash
sudo apt-get install build-essential autoconf automake libtool
```

or under MacOS with [homebrew](https://brew.sh/) using:

```bash
brew install autoconf automake libtool
```

to install the relevant build dependencies.

</details>

#### Debugging BDDs

`OxiDD` and `CUDD` both support dumping the BDD into a file in
[`DOT` Format](https://graphviz.org/doc/info/lang.html). This feature can be
enabled by compiling with the `visualize` feature enabled.

#### Adding Support for BDD Libraries

To add support for a new BDD library, implement the traits `BDDManager` and
`BDD` for the library. The trait definitions can be found under
`model_checker > bdd.rs`.

## Contributing

In general, we tried to design TACO as modular as possible.
You can reuse the whole model checker or only the components you need.
We encourage you to write your own tools based on TACO.

If you have any questions or are facing issues with TACO, feel free to open an
issue.
