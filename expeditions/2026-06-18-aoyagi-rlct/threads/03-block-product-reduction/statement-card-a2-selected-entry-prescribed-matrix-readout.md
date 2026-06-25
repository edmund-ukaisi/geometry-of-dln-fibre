# Statement card - A2 selected-entry prescribed-matrix readout

## Lean Artifact

File: `lean/DLNFibre/DLN/Aoyagi/SelectedEntryOriginalLossLocalMeasure.lean`.

Name:

- `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_prescribedEdgeMatrix_residualProduct_eq_matrix`

## Statement

Lean now proves that a supplied fixed-base matrix family whose
suffix residual product is the selected-entry chart matrix gives the pointwise
selected-entry residual-coordinate readout after realising those matrices as
continuous fixed-base reverse edges.

## Proved

The proof combines:

- the prescribed-matrix recovery theorem
  `paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOfMatrices`;
- the residual-product matrix readout bridge
  `paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_residualProduct_eq_matrix`.

## Not Proved

No construction of the prescribed matrix family, no proof of its
residual-product identity, no construction of the residual-index equivalence,
no source coverage, source-measure transport, normal crossings, pole order, or
RLCT.

## Reproduction

- `reproduction-a2-selected-entry-prescribed-matrix-readout.md`.

## Verification

- From `lean/`:
  `env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryOriginalLossLocalMeasure`
