# Statement card - A4 Case 2 finite raw-pivot chart-family boundary

## Lean target

File:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean
```

Names:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
  .Case2FiniteRawPivotChartRegular

case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
  .Case2FiniteRawPivotTransitionRegular

case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
  .finiteRawPivotChartFamilyBoundary
```

## Claim

When `ChartRegular` means finite selected-entry chart formula plus finite
center-ideal principalization, and `TransitionRegular` means the finite
selected-entry affine overlap pair, the Case 2 residual-block chart-family
boundary is inhabited without using the `True`-predicate witness.

## Inputs

- `hS : 1 <= S`;
- `hcont : J + 1 <= prefixMinNat n (S + 1)`;
- an ordered field-like coefficient type `K`.

## Outputs

- `Case2FiniteRawPivotChartRegular n S J p` for every finite residual-block
  pivot `p`;
- `Case2FiniteRawPivotTransitionRegular (K := K) n hS hcont p q` for every
  ordered pair of finite residual-block pivots;
- a `Case2ResidualBlockChartFamilyBoundary` built from those nontrivial
  predicates.

## Nonclaims

No analytic chart coverage, no analytic transition regularity, no source
production, no suffix production, no source measure or density identification,
no normal crossings, no pole order, and no RLCT extraction.  This is finite
selected-entry algebra only.
