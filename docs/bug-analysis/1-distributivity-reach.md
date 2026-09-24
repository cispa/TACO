# Distributivity in Reachability Specifications

Category: Completeness Bug
Impacted Model Checkers: SMT, ACS, ZCS

In TACO `0.1.0`, the parsing of reachability formulas contained a bug that
mistreated specifications of the form $G (\neg a \vee G(\neg b)) $(negated 
$F(a \wedge F (b))$). Technically, these specifications were not allowed by the
input language specified in the TACO tool paper ([1]), but there were no checks
in place to validate the syntactic constraint.

## Root Cause

Since TACO `0.1.0` only supported reachability properties (see [2]), the
specification parser would always attempt to convert a property into a
reachability property. This worked by first negating the formula and then
attempting to parse constraints inside temporal operators.

In general, a reachability property can be parsed from specifications that in
their negated form use only the finally $F$ operator. The specification inside
the finally would then give the constraints of the set to reach.

However, the extraction logic did not properly take into account that $F$ is not
distributive over $\wedge$, i.e., it does not hold that $F(a \wedge F (b)) 
\not\equiv F(a \wedge b)$. The case of a nested $F$ operator was missing a check
for the context. Therefore, it essentially assumed distributivity.

## Impact

Since all model checkers used the `ReachabilityProperty` type, all of them are
were impacted by this bug. Note though that it is not a soundness bug since any
trace that satisfies $F(a \wedge b)$ is also a trace satisfying
$F(a \wedge F (b))$, therefore counter examples that might be generated are
still valid.

In the benchmark suite in TACO, there is only one benchmark which contained such
a property
([`lmcs20/tendermint-1round-safety.ta`](../../benchmarks/TACO/lmcs20/tendermint-1round-safety.ta)).
For this case however, the property was violated in the benchmark. Therefore,
the correctness of results were not impacted. However, checking the more
complicated property might increase the runtime in practice.

## Mitigation

With the implementation of liveness properties for TACO, the internal
specification types and the extraction logic received a complete overhaul that
now respects distributivity.

[1]: https://doi.org/10.1007/978-3-032-32526-6_19
[2]: https://doi.org/10.1007/978-3-031-71162-6_33
