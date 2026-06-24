# Reproduction - A2 continuity to small loss neighborhood

Date: 2026-06-24.

Status: pen-and-paper reproduced; generic real topology formalised in Lean.

## Target

The finite literal-vs-cleaned comparison needs the local hypothesis

```text
squareSum(F2_x) + squareSum(F3_x) <= 1.
```

This note isolates the elementary topology that supplies such a neighborhood
from centered continuity over `R = real`.

## Generic Argument

Let `eta` be finite and let

```text
f : alpha -> eta -> real
```

be continuous at `x0` as a Pi-valued map, with `f x0 = 0`.  Define

```text
S(x) = sum_c (f x c)^2.
```

Each coordinate projection `x |-> f x c` is continuous at `x0`, so
`x |-> (f x c)^2` is continuous at `x0`.  A finite sum of these functions is
continuous at `x0`, hence `S` is continuous at `x0`.

At the center,

```text
S(x0) = sum_c 0^2 = 0.
```

Since `0 < 1` in the order topology on `real`, `(-infty, 1]` is a
neighborhood of `0`.  Pulling this neighborhood back along `S` gives

```text
eventually x in nhds x0, S(x) <= 1.
```

Equivalently, there is an ambient neighborhood of `x0` on which the finite
coordinate square-sum is at most `1`.

## Two-Family Version

For finite coordinate families

```text
f : alpha -> eta -> real,
g : alpha -> kappa -> real,
```

with `f x0 = 0`, `g x0 = 0`, and both maps continuous at `x0`, apply the
generic result to the disjoint-sum family

```text
F(x) = f(x) ⊕ g(x) : eta ⊕ kappa -> real.
```

The finite square-sum splits over the disjoint sum:

```text
squareSum(F(x)) = squareSum(f(x)) + squareSum(g(x)).
```

Therefore

```text
eventually x in nhds x0,
  squareSum(f(x)) + squareSum(g(x)) <= 1.
```

## Coordinatewise Data Version

The local Aoyagi source-data predicates often store scalar data in the form

```text
for every c, f(x0,c)=0 and x |-> f(x,c) is continuous at x0.
```

This is equivalent to Pi-valued centering and continuity for finite products:
function extensionality gives `f x0 = 0`, and `continuousAt_pi'` assembles
the coordinatewise continuity into `ContinuousAt f x0`.  Lean records both the
one-family and two-family versions of this wrapper.

## Aoyagi Use

For the p. 13 regular block map over `real`, take `f` to be the `F2`
coordinate subfamily and `g` to be the `F3` coordinate subfamily.  The current
Lean slice proves the generic ambient theorem and the coordinatewise-data
wrapper.  A later p. 13-specific wrapper should apply these lemmas to the
actual fixed-base source-data maps, and then weaken/intersect the ambient
neighborhood to the source-rank stratum as needed.

## Boundary

This proves only an ambient topological smallness neighborhood for finite real
coordinate families.  It does not prove source-rank openness, analytic
coordinate status, a local chart inverse, analytic ideal transport,
regular-suspension chart construction, Fubini/polar regular-variable shift,
normal crossings, pole order, or RLCT.
