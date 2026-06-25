# Statement card - A2 residual-factor product

## Declarations

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.residualFactorProduct
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.residualFactorProduct_self
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.residualFactorProduct_castSucc
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.residualProduct_eq_residualFactorProduct_of_residualBlock_eq
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.residualProduct_productCoordinateEdges_succSucc_eq_residualFactorProduct
```

## File

```text
lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean
```

## Statement

`residualFactorProduct C j i` is the ordered endpoint product of supplied
residual factors `C_p : Matrix (kappa p.succ) (kappa p.castSucc)`.

If every suffix transformed Schur residual block below the endpoint `j` equals
the corresponding `C_p`, then

```text
residualProduct E j i = residualFactorProduct C j i.
```

For raw multi-edge p.13 product-coordinate matrices with displayed residual
factor family `C`, and with `i = 0`, this hypothesis is supplied by the existing theorem
`residualBlock_productCoordinateEdges_succSucc`, so

```text
residualProduct E last 0 = residualFactorProduct C last 0.
```

## Role

This makes the intermediate-factor obligation explicit.  Future selected-entry
work can target an honest statement of the form

```text
residualFactorProduct C last 0 = selectedEntryMatrix
```

instead of hiding all factorization content inside an opaque
`residualProduct` hypothesis.

## Boundary

This does not prove the selected-entry residual-product matrix identity, does
not produce the residual factors from Aoyagi source data, does not construct a
fixed-base source chart or residual-index equivalence, and does not prove
source coverage, source-measure transport, normal crossings, pole order, or
RLCT.
