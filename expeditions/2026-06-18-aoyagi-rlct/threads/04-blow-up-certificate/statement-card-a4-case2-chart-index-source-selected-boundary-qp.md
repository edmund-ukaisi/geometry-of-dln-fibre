# Statement card - A4 Case 2 chart-index source-selected boundary/QP bridge

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Names:

- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelectedBoundary_of_chart_case2Succ_updateSelected`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelectedQP_sourceChartMap_of_chart_case2Succ_updateSelected`

## Claim

For a chart index `c` of the Case 2 all-pivot selected-entry finite
certificate, the pivot enumerated by `c` instantiates the existing
source-selected Case 2 supplied-boundary constructor, and the existing
source-selected `Q/P` source-chart-map projection can be applied to that
boundary.

## Inputs Kept Explicit

- displayed Case 2 continuation assumptions `1 <= S`, `S <= L`, and
  `J+1 <= prefixMinNat n (S+1)`;
- the all-pivot certificate chart index `c`;
- pre-state exponent certificates, level invariants, and least-value gap;
- the supplied `Case2ResidualBlockChartFamilyBoundary`;
- residual source coordinates and following-factor data for the `Q/P`
  projection.

## Not Proved

No chart coverage, no analytic atlas construction, no proof of supplied
chart/transition regularity, no non-top-left source-displayed Aoyagi formulas,
no chart production of recurrence or exponent post-data, no successor matrix
or suffix production, no analytic Jacobian/volume theorem, no global normal
crossings, no pole order, and no RLCT extraction.

## Verification

Focused and full checks passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

The sorry audit reported `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build still reports pre-existing warnings in unrelated
Core modules.

Independent xhigh review passed with only a stale-status documentation finding,
now addressed.  Durable artifact:
`review-case2-chart-index-source-selected-boundary-qp-a4.md`.
