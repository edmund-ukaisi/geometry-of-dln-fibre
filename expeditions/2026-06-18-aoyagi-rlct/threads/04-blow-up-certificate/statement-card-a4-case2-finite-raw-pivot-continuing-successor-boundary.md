# Statement card - A4 Case 2 finite raw-pivot continuing successor boundary

## Lean target

File:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean
```

Name:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
  .finiteRawPivotContinuingSuccessorBoundary
```

## Claim

When Case 2 continues from `(S,J)` to `(S,J+1)`, the successor finite
residual-block chart-family boundary can be inhabited by the same nontrivial
finite predicates used in `finiteRawPivotChartFamilyBoundary`: raw-pivot
selected-entry chart regularity and finite affine-overlap transition
regularity.

## Inputs

- `hS : 1 <= S`;
- `hnext : J + 2 <= prefixMinNat n (S + 1)`;
- an ordered field-like coefficient type `K`.

## Output

```text
Case2ResidualBlockChartFamilyBoundary n S (J + 1)
  (Case2FiniteRawPivotChartRegular n S (J + 1))
  (Case2FiniteRawPivotTransitionRegular (K := K) n hS hnext)
```

## Nonclaims

No analytic next-chart construction, no analytic coverage, no analytic
transition regularity, no source production, no suffix production, no source
measure or density identification, no branch termination, no normal crossings,
no pole order, and no RLCT extraction.

This is finite selected-entry algebra only.
