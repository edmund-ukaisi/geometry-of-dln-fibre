# Statement card - A4 Case 2 chart-index Schur transition

## Lean Artifacts

Files:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Names:

- `case2SourceSelectedNormalizedMapOfMem_schurComplement_transition_mul_sq`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelected_schurComplement_transition_mul_sq`

## Claim

For supplied source and target residual-block pivots, the selected-entry target
Schur coordinate satisfies the denominator-cleared identity

```text
x_ab^2 * z_ij = x_ab*x_ij - x_ib*x_aj
```

under the explicit normalised-coordinate overlap hypothesis `x_ab != 0`.

The chart-indexed theorem states the same finite identity for the pivots
enumerated by the Case 2 all-pivot selected-entry certificate.

## Inputs Kept Explicit

- source and target pivot memberships in `case2ResidualBlockPivotEntries n S J`;
- source and target chart indices for the chart-indexed theorem;
- the normalised nonzero denominator;
- ambient off-target row and column complement indices.

## Not Proved

No analytic transition regularity, no chart coverage, no open-neighbourhood
gluing, no source-displayed all-pivot atlas, no successor residual/following
factor production, no analytic Jacobian/volume theorem, no global normal
crossings, no pole order, and no RLCT extraction.

## Verification

Current focused checks passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

Independent xhigh review passed.  Durable artifact:
`review-case2-chart-index-schur-transition-a4.md`.  The sorry audit reported
`0 sorry`, `0 #exit`, `0 native_decide`, and `0 axiom`.  The full build still
reports pre-existing unrelated Core/style warnings.
