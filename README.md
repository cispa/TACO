![GitHub License](https://img.shields.io/github/license/cispa/TACO?style=flat-square)
![GitHub top language](https://img.shields.io/github/languages/top/cispa/TACO?style=flat-square)
[![Continuous Integration](https://img.shields.io/github/actions/workflow/status/cispa/TACO/test.yml?branch=main&label=tests&style=flat-square)](https://github.com/cispa/TACO/actions/workflows/test.yml?query=branch%3Amain)
[![Website Build](https://img.shields.io/github/actions/workflow/status/cispa/TACO/static.yml?branch=main&label=website&color=%2303dbfc&style=flat-square)](https://taco-mc.dev)
[![GitHub Release](https://img.shields.io/github/v/release/cispa/TACO?style=flat-square)](https://github.com/cispa/TACO/releases)
![GitHub Discussions](https://img.shields.io/github/discussions/cispa/TACO?style=flat-square)

# TACO Toolsuite

The Threshold Automata for COnsensus (TACO) model checker tool suite is a
collection of tools to analyze and verify distributed algorithms, modeled as
threshold automata.

You can learn more about threshold automata, the algorithms implemented in TACO
and how to use them on [TACO's web page `taco-mc.dev`](https://taco-mc.dev).

## Documentation & Installation

You can find general information about the structure of TACO on the
[TACO website](https://taco-mc.dev/).

For instructions on how to install the CLI, i.e., `taco-cli` refer to
[the installation page](https://taco-mc.dev/install/).
Once you have installed the CLI you can find a quick start guide
[here](https://taco-mc.dev/usage-cli/).

Alternatively, you can find all the documentation files TACO's website is
generated from in the [`./docs`](./docs) folder.

## Crates

TACO consists of multiple crates:

| Crate                    | Current Version                                                                                                                               | Docs                                                                                                                                          | Description                                              |
| ------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------- |
| taco-acs-model-checker   | [![Crates.io](https://img.shields.io/crates/v/taco-acs-model-checker?style=flat-square)](https://crates.io/crates/taco-acs-model-checker)     | [![Api Docs](https://img.shields.io/badge/docs-api-blue?style=flat-square)](https://taco-mc.dev/dev-docs/taco_acs_model_checker/index.html)   | ACS Model Checker Implementation                         |
| taco-bdd                 | [![Crates.io](https://img.shields.io/crates/v/taco-bdd?style=flat-square)](https://crates.io/crates/taco-bdd)                                 | [![Api Docs](https://img.shields.io/badge/docs-api-blue?style=flat-square)](https://taco-mc.dev/dev-docs/taco_bdd/index.html)                 | High-level interface for BDDs in TACO                    |
| taco-cli                 | [![Crates.io](https://img.shields.io/crates/v/taco-cli?style=flat-square)](https://crates.io/crates/taco-cli)                                 | [![Api Docs](https://img.shields.io/badge/docs-api-blue?style=flat-square)](https://taco-mc.dev/dev-docs/taco_cli/index.html)                 | Command Line Interface for TACO                          |
| taco-display-utils       | [![Crates.io](https://img.shields.io/crates/v/taco-display-utils?style=flat-square)](https://crates.io/crates/taco-display-utils)             | [![Api Docs](https://img.shields.io/badge/docs-api-blue?style=flat-square)](https://taco-mc.dev/dev-docs/taco_display_utils/index.html)       | Utility functions for printing string representations    |
| taco-interval-ta         | [![Crates.io](https://img.shields.io/crates/v/taco-interval-ta?style=flat-square)](https://crates.io/crates/taco-interval-ta)                 | [![Api Docs](https://img.shields.io/badge/docs-api-blue?style=flat-square)](https://taco-mc.dev/dev-docs/taco_interval_ta/index.html)         | Threshold automaton with interval abstraction applied    |
| taco-model-checker       | [![Crates.io](https://img.shields.io/crates/v/taco-model-checker?style=flat-square)](https://crates.io/crates/taco-model-checker)             | [![Api Docs](https://img.shields.io/badge/docs-api-blue?style=flat-square)](https://taco-mc.dev/dev-docs/taco_model_checker/index.html)       | Model Checker Interface and Specifications               |
| taco-parser              | [![Crates.io](https://img.shields.io/crates/v/taco-parser?style=flat-square)](https://crates.io/crates/taco-parser)                           | [![Api Docs](https://img.shields.io/badge/docs-api-blue?style=flat-square)](https://taco-mc.dev/dev-docs/taco_parser/index.html)              | Parser implementations for threshold automata            |
| taco-smt-encoder         | [![Crates.io](https://img.shields.io/crates/v/taco-smt-encoder?style=flat-square)](https://crates.io/crates/taco-smt-encoder)                 | [![Api Docs](https://img.shields.io/badge/docs-api-blue?style=flat-square)](https://taco-mc.dev/dev-docs/taco_smt_encoder/index.html)         | Utility code to setup SMT solvers and encoding functions |
| taco-smt-model-checker   | [![Crates.io](https://img.shields.io/crates/v/taco-smt-model-checker?style=flat-square)](https://crates.io/crates/taco-smt-model-checker)     | [![Api Docs](https://img.shields.io/badge/docs-api-blue?style=flat-square)](https://taco-mc.dev/dev-docs/taco_smt_model_checker/index.html)   | Implementation of the SMT model checker                  |
| taco-threshold-automaton | [![Crates.io](https://img.shields.io/crates/v/taco-threshold-automaton?style=flat-square)](https://crates.io/crates/taco-threshold-automaton) | [![Api Docs](https://img.shields.io/badge/docs-api-blue?style=flat-square)](https://taco-mc.dev/dev-docs/taco_threshold_automaton/index.html) | Basic types for threshold automata                       |
| taco-zcs-model-checker   | [![Crates.io](https://img.shields.io/crates/v/taco-zcs-model-checker?style=flat-square)](https://crates.io/crates/taco-zcs-model-checker)     | [![Api Docs](https://img.shields.io/badge/docs-api-blue?style=flat-square)](https://taco-mc.dev/dev-docs/taco_zcs_model_checker/index.html)   | Implementation of the ZCS model checker                  |

You can find the source code in the respective folder under
[`./crates`](./crates/). You can find a more detailed explanation of the
function of each crate and development dependencies in the
[`Developer Documentation`](https://taco-mc.dev/dev-docs/).

## Questions & Contributing

We tried to design TACO as modular as possible. We hope that this will enable
you to write your own tools for threshold automata.

You will be able to find more information about TACO's internal structure in the
developer documentation.

If you have any questions, feature requests, or something is unclear, feel free
to open an issue or create a discussion on this repository.

If you think TACO is missing a vital feature, feel free to open a PR!
