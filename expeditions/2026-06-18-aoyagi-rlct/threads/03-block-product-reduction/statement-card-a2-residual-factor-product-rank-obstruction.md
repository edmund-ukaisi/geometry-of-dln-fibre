# Statement card - A2 residual-factor product rank obstruction

## Declarations

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.residualFactorProduct_trans
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.rank_residualFactorProduct_le_card_intermediate
```

## File

```text
lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean
```

## Statement

For supplied residual factors `C p`, the ordered factor product splits through
any intermediate residual index:

```text
residualFactorProduct C j i =
  residualFactorProduct C j q * residualFactorProduct C q i
```

whenever `i <= q <= j`.

If the coefficient ring is nontrivial, then

```text
rank (residualFactorProduct C j i) <= card (kappa q).
```

## Role

This formalises the finite-dimensional obstruction behind the residual-product
frontier: a multi-edge residual product factors through every intermediate
residual space, so it cannot generally realize an arbitrary terminal residual
matrix.

## Boundary

No selected-entry matrix identity, no source-factor construction, no
fixed-base source chart, no residual-index equivalence, no source coverage, no
measure transport, no normal crossings, no pole order, and no RLCT.
