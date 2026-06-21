# Review - A4 Case 2 free Cprime continuing branch

Status: reviewed and formalised.

## Scope Check

The proposed target is narrower than a transition theorem.  It proves a
block-product identity for an arbitrary pivot-first chart-coordinate matrix
`C'` and reindexes the lower rows to the continuing `(S,J+1)` domains.

This is the right scope for the next A4 slice because it removes one
unnecessary source-following-factor dependence from the continuing branch
without claiming chart coverage or source construction.

## Fidelity Risks

- Aoyagi writes `C' = Q^-1 C`; proving the identity for arbitrary `C'` is an
  algebraic strengthening.  It is source-compatible only if presented as a
  finite free-coordinate identity, not as a source chart coverage statement.
- The stopped branches and terminal relabels are not involved.
- The corrected exponent post-data package is still supplied/corrected data,
  not produced by the coordinate calculation in this theorem.
- The printed Case 2 vector mismatch remains quarantined.

## Lean Risks

- The theorem should reuse `weightedPivotClearedBlock_mul_verticalBlock` and
  `Matrix.submatrix_mul_equiv`, matching the existing constructed-`C` theorem.
- Avoid defining a second post-pivot residual block; only define the free
  reindexed tail of `C'`.
- If a source-chart package is added, it should be a sibling of the existing
  `sourceChartMap_postPivotNextSameStageProduct_withCorrectedPostData`, not a
  replacement.

## Verdict

The low-level free-`C'` identity and the narrow source-chart package are in
scope.  Do not upgrade `SourceChartFrontierBoundaryPackages` unless the new
field has a clear downstream use.

## Xhigh Checks

Source checker `Erdos` confirmed the source anchors on Aoyagi pp. 19-22:
`Q`, `C'=Q^-1 C`, the displayed `D''' = [1 0; 0 D_{J+1}]`, and the
continuation sentence with `J` increased by one.  The checker accepted the
identity exactly as a finite block adapter

```text
D''' * [C'_0; C'_tail] = [C'_0; E*C'_tail],
```

with the kill condition that "arbitrary `C'`" means arbitrary compatible
displayed pivot-first chart-coordinate data, not source-produced following
data or all pivot charts.

Lean API scout `Mill` independently identified the missing API as a free
post-pivot following-factor tail and a free-`C'` lower-row theorem.  The
landed implementation uses an explicit top/tail split mirroring the existing
source-produced theorem; this is equivalent in scope to the scout's direct
`Cprime.submatrix` proposal.
