# Statement Card - A2 residual block continuity support

Date: 2026-06-25.

## Claim

For a continuous family of fixed-coordinate edge matrices `E(x)`, the
transformed Schur residual factor

```text
residualBlock(E(x), j, p)
```

is continuous at `x0` under the recursive determinant-chart hypotheses at
`x0`.  The ordered residual product

```text
residualProduct(E(x), j, i)
```

is also continuous at `x0`, because it is the `D` field of the suffix state.

In fixed endpoint bases, a continuous reversed edge family `Cedge(x)` has
continuous fixed-coordinate edge matrices, and therefore its transformed
source residual factors are continuous under the same chart hypotheses.

Consequently, the source-dependent multi-edge p.13 product-coordinate edge
family constructed from `CedgeBase(x)` and Euclidean regular coordinates `u`
is continuous at `(x0,u0)`, assuming `CedgeBase` is continuous at `x0` and the
recursive determinant-chart hypotheses hold for the base fixed-coordinate
matrix family at `x0`.

## Lean Artifacts

```text
continuous_productCoordinateRightEndpointMatrix
continuous_productCoordinateMiddleMatrix
continuous_productCoordinateLeftEndpointMatrix
continuousAt_chartLocalSuffixState_residualBlock
continuousAt_chartLocalSuffixState_residualProduct
continuous_matrix_toContinuousLinearMap
paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousAt
paperEndpointFixedBaseContinuousEdges_residualBlock_continuousAt
paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices_continuous
paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices_continuousAt
AoyagiRegularBlockCoordinateIndex.continuous_f2Matrix_euclidean
AoyagiRegularBlockCoordinateIndex.continuous_f3Matrix_euclidean
continuousAt_paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean
continuousAt_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
continuousAt_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase
```

## Inputs Kept Explicit

- finite coordinate and edge index types;
- continuity of the fixed matrix family, or continuity of the underlying
  fixed-base reversed edge family;
- a base point `(x0,u0)` for the source-dependent product family;
- recursive determinant-chart hypotheses at the base point, or the self-base
  hypothesis `CedgeBase x0 = reverseEdge B` for the self-base wrapper.

## Nonclaims

No product chart, source coverage, rank-stratum openness, automatic recursive
chart neighborhood, signed-box pushforward, density/Jacobian transport, normal
crossings, pole order, or RLCT extraction is proved.  The continuity theorem is
local and conditional on the recursive determinant-chart hypotheses at `x0`.

## Verification

Focused direct local Lake builds passed for:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.ChartTopology
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.FixedBasepointChart
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
```

After adding the source-dependent product-family continuity wrappers, full
direct local Lake build passed:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre
```

Repository checks passed:

```text
scripts/sorries
git diff --check
```

The local Lake layout used for this verification keeps `lean/.lake/build`
worktree-local and symlinks the package checkouts in `lean/.lake/packages`,
including `mathlib`, into the shared revision-keyed store.
