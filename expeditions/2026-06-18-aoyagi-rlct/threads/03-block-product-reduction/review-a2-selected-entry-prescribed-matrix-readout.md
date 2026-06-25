# Review - A2 selected-entry prescribed-matrix readout

Date: 2026-06-25.

Reviewer: Linnaeus, xhigh independent checker.

Verdict: PASS.

## Scope

Reviewed the Lean theorem
`paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_prescribedEdgeMatrix_residualProduct_eq_matrix`
in `SelectedEntryOriginalLossLocalMeasure.lean`, plus the reproduction and
statement card for the prescribed-matrix readout bridge.

## Findings

No blocking findings.

The Lean theorem is honest: it assumes the residual-index equivalence and the
exact residual-product matrix identity for `Ebase (chartMap pivot y)`, realises
`Ebase` as a continuous reverse-edge family, recovers the prescribed
fixed-base matrices via
`paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOfMatrices`,
and delegates to the residual-product matrix readout bridge.

The theorem is thin API packaging, but useful when downstream source-chart
algebra is naturally stated in fixed-base edge matrices.  It does not advance
source coverage.

Low wording risks were fixed after review:

- the reproduction now says future source-chart algebra supplies a fixed-base
  edge-matrix family, not a source chart;
- the claims note now says the theorem is a supplied-matrix bridge;
- the statement card avoids the redundant phrase "supplied prescribed".

## Verification

Reviewer read-only checks:

- `cd lean && LEAN_NUM_THREADS=1 lake env lean DLNFibre/DLN/Aoyagi/SelectedEntryOriginalLossLocalMeasure.lean`
- `git diff --check`

Controller verification:

- `env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryOriginalLossLocalMeasure`
