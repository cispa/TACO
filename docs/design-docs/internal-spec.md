# Internal Specification Format

## What the theory supports

While our theory supports arbitrary ELTL formulas via automata construction, the
benchmarks (at least in theory) mostly do not need the expensive construction.

The theory currently supports 3 main simplified specification types:

- _Reach_: where the error path is described by a formula of the form
  `init && <>(p)`
- _Ensure_: where the error path is described by a formula of the form
  `init && [](p)`
- _Repeat_: where the error path is described by a formula of the form
  `init && <>(p1 && [](p2))`

The goal of the internal specification format is now to decompose arbitrary
formulas into model checker runs on specifications that fall into one of these
categories.

## Target Type

To represent the three different constraint types we introduce the type
`ErrorTarget`:

```Rust
pub enum ErrorTarget {
    /// `<>(set)`: some configuration in the set is reachable
    Reach(UpwardsClosedSet),
    /// `[](set)`: there is an (infinite) run that never leaves the set
    Ensure(UpwardsClosedSet),
    /// `<>(pre && [](inv))`: there is an (infinite) run that reaches a
    /// configuration in `pre` and never leaves `inv` afterwards
    Repeat {
        /// Set of configurations to reach
        pre: UpwardsClosedSet,
        /// Set of configurations that is never left after reaching `pre`
        inv: UpwardsClosedSet,
    },
    /// No temporal part: the atom is only a restriction on the initial
    /// configuration
    Top,
}
```

and the type `ErrorAtom` to represent the conjunction of an initial restriction
and a goal type.

```Rust
pub struct ErrorAtom {
    /// Restriction on the initial configuration
    init_restriction: InitRestriction,
    /// Temporal part of the atom
    target: ErrorTarget,
}
```

Here `InitRestriction` is a type which represents a conjunction of initial
constraints.

Using this type, we can use the type `ErrorFormula`

```Rust
pub type ErrorFormula = Disjunction<ErrorAtoms>;
```

Which represent a disjunction over `ErrorAtom`s. Each `ErrorAtom` can then be
checked in a separate model checker query. If all queries return safe, the
automaton is safe.

Note that conjuncts of error atoms cannot be supported in the same way. This is
because a conjunct requires the property to be satisfied on the same run.
However, in some cases, for example for a specification of the form
`[](a) && [](b)` one can rewrite the specification into a single atom
(`[](a && b)`). The rewrite rules are elaborated in the next section.

## Supported Rewrites

Ideally, when decomposing an arbitrary ELTL formula into queries, we would like
to obtain as little queries as possible, and we would like to avoid an automaton
construction wherever possible.

Therefore, we apply rewrite rules as far as possible. These rewrite rules are
derived from LTL equivalences:

### LTL Distributive Laws

- `<>(a || b)` <-> `<>(a) || <>(b)` <-> `<>(<>(a) || b)`
- `[](a && b)` <-> `[](a) && [](b)`

Note that in particular, it does not hold that `<>(a) && <>(b)` is equivalent to
`<>(a && b)` (since this requires a point where a and b holds and not just some
point where a holds and some point where b holds). Therefore, formulas
containing multiple `<>` in conjunction cannot be converted into an internal
specification.

### Initial Constraints

Note that an initial constraint is built from 3 different types:

- Location Constraints: i.e., constraints over the initial number of processes
  in a location
- Variable Constraints: i.e., constraints over the initial value of variables
- Parameter Constraints: i.e., further restrictions on parameter values

In the internal specification format they are represented as:

```Rust
pub struct InitRestriction {
    /// Conjunction of conditions on the parameters
    precondition_par: Conjunction<BooleanExpression<Parameter>>,
    /// Conjunction of conditions on the initial distribution of processes in
    /// the threshold automaton
    precondition_loc: Conjunction<BooleanExpression<Location>>,
    /// Conjunction of conditions on the initial valuation of the shared
    /// variables
    precondition_var: Conjunction<BooleanExpression<Variable>>,
}
```

These constraints are considered as a conjunction (since in the automaton these
entries are also conjuncts). Therefore, if a disjunction appears in an initial
constraint and the the initial restriction does have elements in other types
of constraints, it has to be split in multiple model checking runs.
