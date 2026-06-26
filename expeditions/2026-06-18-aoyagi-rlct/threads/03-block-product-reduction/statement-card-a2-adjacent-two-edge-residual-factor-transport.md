# Statement card - A2 adjacent two-edge residual-factor transport

## Claim

The explicit residual-factor product over one supplied edge is that factor.
The explicit residual-factor product over an adjacent two-edge window in a
longer chain is the ordered product of the two visited factors. After endpoint
reindexing, its submatrix is the product of the two reindexed factors.

## Lean artifacts

File:

```text
lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean
```

Theorems:

```lean
ChartLocalSuffixState.residualFactorProduct_one_edge_eq_factor
ChartLocalSuffixState.residualFactorProduct_adjacent_two_eq_mul
ChartLocalSuffixState.residualFactorProduct_adjacent_two_submatrix_eq_mul
```

## Proved inputs

- `residualFactorProduct_castSucc`, the one-step unfold.
- `residualFactorProduct_self`, the endpoint identity.
- `residualFactorProduct_trans`, splitting through an intermediate endpoint.
- `Matrix.submatrix_mul_equiv`, reindexing of matrix products.

## Supplied inputs

For the submatrix theorem, callers supply endpoint equivalences for the
right, middle, and left endpoints of the adjacent two-edge window.

## Nonclaims

No fixed-base endpoint equivalence is constructed. No retained-passive full
suffix is collapsed to the adjacent window. No Case 2 factor identity,
selected-entry readout, pivot nonzero condition, source chart, pushforward,
Jacobian theorem, original-loss comparison, normal crossings, pole order, or
RLCT extraction is proved.
