# A2 Case 2 source-stratum-supported continuous-density small-box two-sided iff

## Claim

Under the explicit uniform Case 2 source-rank equations, the chart-produced
selected-entry source measure is supported on the source-rank stratum.  The
new Case 2 continuous-density small-box two-sided iff can therefore be stated
over the open neighborhood `U` itself, not over `U ∩ sourceStratum`.

Both sides of the iff are rewritten:

```text
actual loss-density integral over (mu.restrict U).prod nu is finite
iff
residualNegPowerIntegrableOn (fun E => E) U mu t.
```

## Measure calculation

Let

```text
S  = sourceStratum,
mu = Measure.map sourceChart sourceMeasure.
```

The already-proved support theorem gives

```text
mu.restrict S = mu
```

from the explicit rank equations

```text
finrank range(paperTotalMap W2 B2) = r,
r + card tau = rEdge 0,
forall yNext,
  r + rank(case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext) = rEdge 1.
```

For any open `U`, `U` is measurable, and Mathlib gives

```text
mu.restrict (U inter S) = (mu.restrict S).restrict U.
```

Combining these equalities:

```text
mu.restrict (U inter S) = mu.restrict U.
```

The product-measure integral side rewrites by this equality.  The residual
integrability side also rewrites by the same equality, because
`residualNegPowerIntegrableOn` is definitionally a finite integral over
`mu.restrict source`.

## Boundary

This is only support bookkeeping for the same chart-produced measure.  The
loss comparison hypotheses remain on `nhdsWithin base sourceStratum`.  The rank
equations are hypotheses; no source-rank coverage, source/image equality,
exact-rank openness, original source-prior transport, Jacobian comparison,
normal crossings, pole order, or RLCT is proved.
