# Reproduction - A2 Case 2 chart-produced density continuous-at finite integral

## Shape

The existing Case 2 chart-produced finite-integral theorem has the local
density bounds as explicit inputs:

```text
forall eventually x in nhdsWithin base localSource,
  forall u in ball 0 Rreg, 0 <= density (x,u)

forall eventually x in nhdsWithin base localSource,
  forall u in ball 0 Rreg, density (x,u) <= Creg.
```

It also takes the regular-coordinate radius `Rreg`, the bound `Creg`, and
`0 <= Creg`.

The target is the radius-shrinking version.  Replace those supplied density
bounds by:

```text
ContinuousAt density (base, 0)
0 < density (base, 0)
0 < Rmax.
```

The conclusion returns a smaller radius `R`, a bound `C`, and an open
neighborhood `U`:

```text
exists R C U,
  0 < R and R <= Rmax and 0 <= C and IsOpen U and base in U and
  lintegral over ball 0 R is finite.
```

All source data, endpoint equivalences, residual radii, the Case 2 critical
inequality, Haar measure on the regular variables, and the local loss lower
bound remain explicit.

At the Lean boundary this also retains the fixed-base finite-dimensional
endpoint assumptions, `hS`, `hcont`, `hnext`, `U0`, `hU0`,
`[MeasurableSpace EdgeFamily]`, `[OpensMeasurableSpace EdgeFamily]`,
`[BorelSpace EdgeFamily]`, `0 < creg`, `0 < t`, and `ν.IsAddHaarMeasure`.

## Calculation

Let

```text
localSource :=
  paperEndpointFixedBaseRetainedPassiveP13LocalSource W2 B2 U0 hU0
    (fun E : EdgeFamily => E).
```

Apply the relative density-bounds lemma to the topological space of source
edge families, the regular-coordinate Euclidean space, the set `localSource`,
and the point `base`:

```text
exists_pos_radius_le_eventually_nhdsWithin_density_bounds_of_continuousAt_pos
```

with `Rmax`.  This produces

```text
R, C
0 < R
R <= Rmax
0 <= C
eventual nonnegativity of density on ball 0 R
eventual upper bound density <= C on ball 0 R.
```

The existing local loss lower bound is assumed on the larger ball `ball 0
Rmax`.  Since `R <= Rmax`, the metric ball inclusion gives

```text
ball 0 R subset ball 0 Rmax.
```

Thus the loss lower bound restricts to `ball 0 R`.

Now invoke the existing Case 2 chart-produced finite-integral theorem with

```text
Rreg := R
Creg := C.
```

The theorem returns an open source neighborhood `U` and finiteness of the
negative-power integral over `ball 0 R`.  Package `R`, `C`, and `U` with the
radius and bound inequalities produced by the density-shrinking lemma.

## Boundary

This removes only the supplied local density nonnegativity and boundedness
fields, replacing them by continuity and positivity of the same transported
density at the chart center.  It does not construct that density from an
original prior, prove a Jacobian comparison, identify an external source
measure, construct endpoint equivalences, prove source-rank coverage, prove
normal crossings, compute pole order, or extract RLCT.

## Proved / Assumed / Deferred

**Proved by this reproduction.** Positive continuity of the density at the
chart center implies the density hypotheses needed by the existing Case 2
chart-produced finite-integral theorem after shrinking the regular-coordinate
radius.

**Assumed.** The existing Case 2 source data, endpoint equivalences, the
regular Haar measure, positive residual radii, the Case 2 critical inequality,
and the local loss lower bound on `ball 0 Rmax`.

**Deferred.** Construction and provenance of endpoint equivalences, original
prior transport, Jacobian comparison, source-rank coverage, normal crossings,
pole order, and RLCT extraction.
