# CHANGELOG

<!--
    Format & guidelines for editing this changelog see:
    https://keepachangelog.com/en/1.1.0/
-->

## [Unreleased]

### Fixed

- doc images as `.webp` and naming of TACO (toolsuite / model checker)
  consistent (#3)
- replaced `localhost` reference in `sitemap.xml` and `robots.txt` (#2)

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
