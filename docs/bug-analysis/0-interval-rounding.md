# Bug: Issue in Interval Rounding Logic

Category: Completeness Bug
Impacted Model Checkers: ACS, ZCS

In TACO `0.1.0` the implementation of the computation of interval borders could
lead to potentially cascading rounding errors, that could have potentially
resulted in counter-examples being missed.

## Root Cause

The ACS and ZCS model checkers rely on the computation of what in TACO is called
the `IntervalThresholdAutomaton`, which in essence is a threshold automaton with
parametric interval abstraction applied to it (see [1],[2],[3]).

The borders of the intervals are derived from the rule guards. In the
theoretical presentations, these guards are of the form:

$$
    c x > c_0 \cdot n + c_1 \cdot c_2 ...
$$

or

$$
    c x \leq c_0 \cdot n + c_1 \cdot c_2 ...
$$

where $x$ is a shared variable and $n$ a parameter. For the coefficients, the
domain is unclear: While most work use integers (i.e., $c, c_0, c_1, ... 
\in \mathbb{Z}$), some use rational coefficients (i.e., $c, c_0, c_1, ... 
\in \mathbb{Q}$) [4]. However, note that the model only considers integer
solutions.

In real-world benchmarks, the constraints do not appear in this shape but are
general combination of constrains using $>, \leq$ but also
$<, \geq, \neq$ or $=$.

TACO internally uses a custom `Fraction` type, and rewrites the formula such
that only variable $x$ appears on the left side. Previously, before converting
into the `Fraction` type, the comparison operators where canonicalized by adding
one to the left side. However, this was done without taking the factor $c$ into
account. This could lead to spurious rounding errors.

However, no instance of such a behavior was found on the benchmark set, as it
required a rational factor $c$.

## Impact

On the benchmark files, there was no instance found where the flawed rounding
logic impacted the intervals constructed. Therefore, the general benchmark
results presented in [4] should remain valid, although some benchmarks do have
additional intervals and therefore some performance impact might be observed.

## Mitigation

The new conversion to interval automata no longer converts the comparison
operators, instead, it supports $>, \leq, <, \geq$. This then required the
insertion of additional intervals (that represent the shared variable having the
exact value of the threshold) and additional logic on the interval type.

Most importantly, intervals now need to be checked whether they contain an
integer (as otherwise spurious checks would always fails for the ZCS model
checker). An empty interval can occur if, for example, $1$ and $2$ are interval
borders for a variable and the intervals $[1,1],]1,2[,[2,2]$ are added to the
order. Here, the interval $]1,2[$ is empty, therefore, it is discarded and
instead the first interval is changed to $[1,2[$.

## Limitations

An interval order only fixes the relative order of the interval borders, not
their exact parameter values. Therefore, an interval can still be empty for
some, but not all, parameter valuations that satisfy the order:

- An exact interval $[b,b]$ with a rational border $b$ is empty if $b$ does not
  evaluate to an integer, e.g., $[\frac{n}{2},\frac{n}{2}]$ for odd $n$.
- An open interval $]b,b'[$ is empty if $b' = b + 1$, e.g., $]f,n[$ for
  $n = f + 1$.

Abstract runs can only move between adjacent intervals. So, for such a
valuation, every run crossing the empty interval is spurious, and a counter
example that requires this valuation is missed.

This does not affect the benchmarks, as their threshold automata are
multiplicative: multiplying a solution by a factor again yields a solution.
Consequently, for every counter example there exists a valuation for which all
intervals of the order are inhabited. For threshold automata that are not
multiplicative, the ACS and ZCS model checkers can be incomplete.

[1]: https://doi.org/10.1007/978-3-031-71162-6_33
[2]: https://doi.org/10.1007/S100090050040
[3]: https://doi.org/10.1109/FMCAD.2013.6679411
[4]: https://doi.org/10.1007/978-3-031-71162-6_33
[5]: https://doi.org/10.1007/978-3-032-32526-6_19
