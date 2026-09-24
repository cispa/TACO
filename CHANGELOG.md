# CHANGELOG

<!--
    Format & guidelines for editing this changelog see:
    https://keepachangelog.com/en/1.1.0/
-->

## [Unreleased]

### Fixed

- grant information for the development of TACO (#6)
- update the README and fix developer documentation links (#5)
- doc images as `.webp` and naming of TACO (toolsuite / model checker)
  consistent (#3)
- replaced `localhost` reference in `sitemap.xml` and `robots.txt` (#2)
- fix clippy issues with 1.95 (#8)
- remove old default timeout that caused timeout for smoke tests not be set (#9)
- fixed bug in abstract interval extraction (see
  [Bug Report 0](./docs/bug-analysis/0-interval-rounding.md)) (#10)
- fixed missing distributivity check (see
  [Bug Report 1](./docs/bug-analysis/1-distributivity-reach.md)) (#10)

### Added

- Elaborate on the function of the different preprocessors (#6)
- upgrade CI pipeline & Dockerfile to Rust 1.95 (#8)
- improved artifact evaluation README (#9)
- artifact README in CAV format (#9)
- new `InternalSpec` to prepare support for liveness specifications (#10)
- `UpwardsClosedSet` with extraction support from `LIAVariableConstraint` to
  unify interval extraction and specification extraction (#10)
- implement proper reporting for specifications where the model checker could
  not determine whether the TA is safe (#10)
- upgrade base image to Fedora 44 (#10)

### Removed

- `ReachabilitySpec` type in favor of `InternalSpec` to prepare support for
  liveness specifications (#10)
- Removed fairness constraints from liveness specifications in
  `TACO` benchmarks (#10)

## [v0.1.0]

### Added

- basic data types for threshold automata
- standardized configuration interface for SMT solvers and functionality to
  encode basic threshold automaton data types
- simple high-level interface for interacting with BDD libraries
- parser for TLA^+ subset and ByMC specification format
- SMT, ACS and ZCS model checkers for threshold automata
- CLI interface to interact with model checkers

[unreleased]: https://github.com/cispa/TACO/compare/v0.1.0...HEAD
[v0.1.0]: https://github.com/cispa/TACO/releases/tag/v0.1.0
