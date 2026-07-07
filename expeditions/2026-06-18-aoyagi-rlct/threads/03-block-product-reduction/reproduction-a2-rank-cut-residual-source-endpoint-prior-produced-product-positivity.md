# A2 rank-cut residual source from endpoint prior with produced product positivity

## Object-level calculation

The previous endpoint-prior rank-cut residual-source theorem has one remaining
theta-side hypothesis:

```text
forall^ae z with respect to coordinateSourceMeasure.restrict V,
  0 < productResidual(z).
```

The with-following coordinate-source finite-integral theorem already produces
an open shrink `Vpos` around the base point with

```text
forall^ae z with respect to coordinateSourceMeasure.restrict Vpos,
  0 < productResidual(z),
```

under the local source-density hypotheses

```text
ContinuousAt (sourceImageDensity o sourceChart) z0,
(sourceImageDensity (sourceChart z0)) < infinity,
Rres_i > 0,
```

and the same determinant-sector, pivot, following-factor determinant, and
critical-exponent assumptions.

To consume this in the rank-cut theorem, run the existing endpoint-prior
rank-cut theorem with ambient open set `G := Vpos`.  It returns

```text
W subset Vpos,
V subset W.
```

Thus `V subset Vpos`.  For any measure `mu`,

```text
mu.restrict V <= mu.restrict Vpos,
```

so `mu.restrict V` is absolutely continuous with respect to
`mu.restrict Vpos`.  Applying absolute-continuity transfer to the a.e.
positivity on `Vpos` gives the exact product-residual positivity on `V`
required by the endpoint-prior rank-cut residual-source package.

The residual readout used by the source finite-integral theorem is
definitionally

```text
case2PassiveThetaWithFollowingFactorProductResidualReadout
```

after unfolding its definition, so no mathematical comparison theorem is being
introduced here.

## Boundary

This removes only the explicit theta-side product-residual positivity
hypothesis from the endpoint-prior rank-cut residual-source chain.  It still
does not prove endpoint-reference Haar transport, determinant/raw Haar
transport, source-prior transport, source-density lower bounds, prior-density
upper bounds, source-rank or analytic-atlas coverage, normal crossings, pole
order, or RLCT extraction.
