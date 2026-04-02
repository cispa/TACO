# Advanced Configuration

## Using Configuration Files

If you want to have fine-grained control over components like the SMT solver,
instead of chaining a long list of arguments, you can instead write a
configuration file in `.yaml` format.

The file can then be passed to TACO by using the `-c`/`--config-file` flag.

(specifying-preprocessors)=

### Specifying Preprocessors

Before model checking a threshold automaton, TACO will use different
preprocessors to simplify the automaton. To understand the usefulness of
preprocessors, it is important to note that the preprocessing is not only
executed once per automaton but instead at least once per property that is being
verified.

This can be helpful because many correctness properties have the form "If no
process starts with input 0, then the algorithm does not accept 0". When
verifying such a property, one assumes that no process starts in the location
corresponding to an input of 0. This means that in the exploration, one does not
need to consider this input location (assuming there is no incoming transition).
In this case, the location would be removed by the preprocessor
`DropUnreachableLocations`.

Currently, the following preprocessors are available:

- `DropSelfLoops`: Removes self-loops that do not contain variable updates. Such
  loops are not useful as they do not change the configuration. Therefore, they
  can be safely disregarded during verification.
- `DropUnreachableLocations`: This preprocessor does reachability analysis: It
  constructs the underlying directed graph of the automaton from the initial
  states (ignoring rule guards) and removes locations that cannot be reached in
  the graph. Locations that are removed cannot be reached from any of the
  initial locations and can therefore be safely disregarded.
- `ReplaceTrivialGuardsStatic`: Replaces rule guards, which are always enabled,
  with `true`. This preprocessor only works for some known patterns.
- `ReplaceTrivialGuardsSMT`: Replaces rule guards, which are always enabled,
  with `true`. This preprocessor uses the SMT solver to determine which guards
  can be true. The outcome of SMT queries for a specific guard is cached during
  preprocessing to decrease the number of SMT queries.
- `RemoveUnusedVariables`: Removes any variables that do not appear in any rule.
  This preprocessor is mostly useful after other preprocessors have already
  eliminated locations and rules.
- `DropUnsatisfiableRules`: Removes rules with guards that can never be
  satisfied. Analogous to `ReplaceTrivialGuardsSMT`, this preprocessor uses SMT
  solvers to determine whether a guard can be satisfied under the current
  resilience condition. If this is not the case, the rule is removed.
  This preprocessor has not proven effective in practice. Therefore, it is
  disabled by default.
- `CollapseLocations`: Collapse locations that all have the same incoming rules.
- `CheckInitCondSatSMT`: Checks whether the initial conditions of a threshold
  automaton are satisfiable first.

(specifying-preprocessors)=

#### Specifying Preprocessors

By default TACO will use `ReplaceTrivialGuardsSMT`,`DropSelfLoops`,
`DropUnreachableLocations`, `CheckInitCondSatSMT` and `RemoveUnusedVariables`.
Note that preprocessors that rely on the SMT solver, like
`ReplaceTrivialGuardsSMT` can potentially have
significant overhead. You can configure which preprocessors to use by
specifying the `preprocessors` field:

```yaml
preprocessors:
  - DropSelfLoops
  - DropUnreachableLocations
  - ReplaceTrivialGuardsStatic
  - ReplaceTrivialGuardsSMT
  - RemoveUnusedVariables
  - DropUnsatisfiableRules
  - CollapseLocations
```

(using-a-custom-smt-solver)=

### Using a Custom SMT Solver

TACO can work with all SMT solvers that

- support the [SMTLIB2](https://smt-lib.org/language.shtml) input language and
- can be started in interactive mode

You can configure TACO to use a custom SMT solver by passing it a configuration
file of the form:

```yaml
smt:
  # Command to start the SMT solver
  command: "z3"
  # Arguments to pass to the SMT solver at startup
  # (solvers must be started in interactive mode with SMTLIB2 as input format)
  args:
    - "--smt2"
    - "-in"
  # Options to set after the starting the SMT solver
  options:
    - parallel: true # corresponds to setting (parallel: true)
```

The example configuration above instructs TACO to start an SMT solver by using
the command `z3` with arguments `--smt2` and `-in` and then sets the `parallel`
option of the solver to `true`.

### Configuring the BDD Backend

Analogously to the configuration for SMT solvers, you can also configure the BDD
backend. For example, if you want to try the performance of TACO's ZCS model
checker with the `Sift` reordering method, you can append the following
configuration to your config file:

```yaml
bdd:
  Cudd:
    reorder_method: Sift
```

### More Options

:::{important}
In general TACO supports all file formats that are supported by the
[serde](https://serde.rs/) crate. To parse configuration, we let
[serde](https://serde.rs/) automatically derive parsers from the relevant
configuration types, and we have not yet documented all available options.

The current list of supported configuration file options is therefore still
very much incomplete. If you have the need for a specific configuration, feel
free to reach out.
:::

(logger-configuration)=

### Logger Configuration

To configure the log output for TACO, you can use the `--logger-config-file`
flag and pass a configuration file in the
[`log4rs`](https://github.com/estk/log4rs) format.
