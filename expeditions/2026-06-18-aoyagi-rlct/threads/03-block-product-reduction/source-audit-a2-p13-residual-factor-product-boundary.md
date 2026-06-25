# Source audit - A2 p.13 residual-factor product boundary

Date: 2026-06-25.

Auditor: xhigh source/API scout `Hilbert`.

## Question

Does Aoyagi's p.13 displayed residual-product term support a stronger
multi-edge selected-entry readout theorem in the current Lean API?

## Verdict

Not without additional supplied finite data.  The source-backed elementary
theorem is the p.13 residual product as an ordered product of compatible
intermediate residual factors.  The selected-entry terminal matrix identity
requires a separate product identity and a residual-index equivalence.

## Source/API Read

Aoyagi p.13 displays the product-reduction lower-right block as the residual
product term

```text
prod_s C^(s) - F3 F2.
```

The current Lean API represents the cleaned residual product by

```text
ChartLocalSuffixState.residualProduct E last 0
```

and the explicit intermediate-factor version by

```text
ChartLocalSuffixState.residualFactorProduct C last 0.
```

The matching source-backed theorem is

```text
ChartLocalSuffixState.residualProduct_productCoordinateEdges_succSucc_eq_residualFactorProduct
```

It says that raw p.13 product-coordinate edge matrices whose lower-right
residual factors are the supplied compatible family `C p` have suffix
residual product equal to the explicit ordered product of those factors.

The fixed-base Euclidean product-coordinate constructor also has the named
consumer

```text
paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean_residualProduct_eq_base
```

which preserves the base suffix residual product by choosing those compatible
factors from the base transformed Schur residual blocks.

## Missing Stronger Input

The stronger selected-entry target would need an explicit finite identity of
the form

```text
ChartLocalSuffixState.residualFactorProduct C last 0 =
  AoyagiResidualBlockCoordinateIndex.matrix
    (fun c => SelectedEntrySignedBox.CenterCoord.chartMap pivot y (e c))
```

with an explicit residual-index equivalence `e`.  A terminal selected-entry
matrix alone is not enough in the multi-edge case, because the product must
factor through every intermediate residual index type.

## Controller Consequence

Do not state a multi-edge theorem that realizes an arbitrary selected-entry
terminal matrix through `residualProduct`.  Future selected-entry work should
either:

- supply compatible factors `C y p`, a residual-index equivalence `e`, and the
  product identity above; or
- stay at the already-proved one-edge selected-entry readout, where there are
  no intermediate residual factors.

This audit does not construct source factors, prove source chart coverage,
identify source measures, produce normal crossings, prove pole order, or
extract RLCT.
