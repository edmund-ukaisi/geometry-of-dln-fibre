# Statement card - A4 Case 2 all-pivot source-selected chart adapter

## Lean Artifacts

Files:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Names:

- `Case2ResidualBlockSelectedEntryChartFamilyData.standard_value_eq_sourceSelectedChartMapOfMem`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartPoint`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.chartMap_sourceChartPoint_eq_sourceSelectedChartMapOfMem`

## Claim

For each chart of the Case 2 all-pivot selected-entry finite certificate, the
chart map at the standard source point `(u, residual)` is exactly the existing
source-selected Case 2 chart map for the pivot enumerated by that chart.

## Source Role

This connects the finite all-pivot selected-entry microcertificate over
Aoyagi's Case 2 residual-block center to the existing source-selected finite
algebra for a supplied residual-block pivot.

## Inputs Kept Explicit

- Case 2 displayed continuation assumptions `1 <= S` and
  `J+1 <= prefixMinNat n (S+1)`;
- the finite chart index `c`;
- the selected variable `u` and residual source coordinates.

## Not Proved

No source production of successor matrices, suffix products, arbitrary-pivot
paper formulas, analytic atlas coverage, transition regularity,
Jacobian/volume theorem, analytic/global normal-crossing theorem beyond the
existing finite selected-entry formal certificate, pole order, or RLCT.

## Verification

Focused checks passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
```

Full gate passed with pre-existing unrelated warnings:

```text
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

The sorry audit reported `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.

Xhigh independent review passed with no blocking findings.  Durable artifact:
`review-case2-all-pivot-and-rowindex-source-bridges-a4.md`.
