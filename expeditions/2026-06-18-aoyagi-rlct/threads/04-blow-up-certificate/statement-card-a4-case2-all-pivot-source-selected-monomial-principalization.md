# Statement card - A4 Case 2 all-pivot source-selected monomial/principalization adapter

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Names:

- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.centerIdeal_sourceSelectedChartMap_eq_span_singleton`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.loss_sourceChartPoint_eq_sourceSelectedCenterSq`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.lossUnit_sourceChartPoint_eq_sourceSelectedUnitFactor`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.jacobianPrior_sourceChartPoint_eq_sourceSelectedDet`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.loss_monomial_sourceChartPoint_sourceSelected`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.jacobianPrior_monomial_sourceChartPoint_sourceSelected`

## Claim

For any chart `c` of the Case 2 all-pivot selected-entry finite certificate,
the pivot selected by `c` can be used in the existing source-selected Case 2
chart map, and the certificate's finite center principalization, loss monomial
identity, loss unit, formal Jacobian/prior determinant, and Jacobian/prior
monomial identity can all be stated in those source-selected names.

## Inputs Kept Explicit

- displayed Case 2 continuation assumptions `1 <= S` and
  `J+1 <= prefixMinNat n (S+1)`;
- the finite chart index `c`;
- the selected chart variable `u`;
- residual source coordinates `residual : Nat × Nat -> K`.

## Not Proved

No arbitrary-pivot source production, no claim that Aoyagi displays every
non-top-left chart, no successor matrix or suffix production, no recurrence or
exponent post-data production, no analytic chart coverage or transition
regularity, no analytic Jacobian/volume theorem, no global normal-crossing
certificate, no pole order, and no RLCT extraction.

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

Independent xhigh review passed with no blocking findings.  Durable artifact:
`review-case2-all-pivot-source-selected-monomial-principalization-a4.md`.
