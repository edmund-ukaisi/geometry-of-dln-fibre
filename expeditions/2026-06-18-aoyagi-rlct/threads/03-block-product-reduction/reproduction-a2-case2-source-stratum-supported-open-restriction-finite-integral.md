# A2 Case 2 source-stratum-supported open-restriction finite integral

## Question

The source-stratum-bound Case 2 chart-produced finite-integral theorem gives
local finiteness for the selected-entry chart-produced measure restricted to

```text
U intersect sourceStratum.
```

After the support theorem, the same chart-produced measure is already
supported on `sourceStratum` when the explicit Case 2 rank equations are
supplied.  The question is whether the finite-integral conclusion can be
restated over the open-neighborhood restriction `U` itself.

## Measure calculation

Let

```text
mu = Measure.map sourceChart sourceMeasure,
S = sourceStratum.
```

The support theorem gives

```text
mu.restrict S = mu.
```

For any open `U`, hence any measurable `U`, Mathlib's restriction identity
gives

```text
(mu.restrict S).restrict U = mu.restrict (U intersect S).
```

Combining these two equalities yields

```text
mu.restrict (U intersect S) = mu.restrict U.
```

Therefore any nonnegative integral already proved finite over
`(mu.restrict (U intersect S)).prod nu` is the same integral over
`(mu.restrict U).prod nu`.

## Case 2 inputs

The support equality is not automatic.  The corollary keeps the explicit rank
support hypotheses:

```text
finrank range(paperTotalMap W2 B2) = r,
r + card tau = rEdge 0,
forall yNext,
  r + rank(case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext) = rEdge 1.
```

The old source-stratum-bound theorem still supplies the open set `U` and the
finite integral over `U intersect sourceStratum`.  The new corollary only
changes the measure restriction after the support calculation.

## Boundary

This proves a finite-integral restatement for the same chart-produced measure
under explicit source-rank support hypotheses.  It does not prove source-rank
coverage, selected-entry image equality, exact-rank openness, source-prior or
Jacobian transport, analytic atlas construction, normal crossings, pole order,
RLCT, or a numerical successor selected-entry matrix rank.
