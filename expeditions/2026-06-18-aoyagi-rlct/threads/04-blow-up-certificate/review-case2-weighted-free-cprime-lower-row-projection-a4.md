# Review - A4 Case 2 weighted free Cprime lower-row projection

Status: reviewed and formalised.

## Scope Check

The target is finite block algebra:

```text
(blockdiag(b0,diag b) * blockdiag(1,E) * [Ctop;Ctail])_lower
  = diag(b) * (E*Ctail).
```

The Aoyagi-specific theorem only reindexes this identity to the continuing
`(S,J+1)` row and column domains.

## Risks

- Do not drop the lower-row diagonal weights.
- Do not claim the pivot row or a full successor product.
- Do not use this to infer recurrence/exponent post-data.
- Do not attach next residual-center nonemptiness without the separate
  `J+2 <= prefixMinNat n (S+1)` hypothesis.

## Verdict

The generic row-weight lemmas, displayed Case 2 specialization, and
supplied-boundary wrapper are in scope.

## Xhigh Checks

Source checker `Beauvoir` green-lit the theorem as a finite lower-row
projection of Aoyagi's displayed weighted right side
`diag(b') D''' C'`.  The accepted statement keeps the lower-row weight
diagonal explicit and excludes the pivot row.

Lean API scout `Dirac` recommended the same row-scaling abstraction and a
wrapper
`Case2DisplayedSuppliedChartFamilyBoundary.postPivotWeightedFreeCprimeNextSameStageProduct`.
The landed implementation keeps the generic reindexed helper already proved by
the controller probe and adds that supplied-boundary wrapper.
