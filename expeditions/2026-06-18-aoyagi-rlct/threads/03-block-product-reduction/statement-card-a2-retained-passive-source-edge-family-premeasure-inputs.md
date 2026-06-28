# Statement card - A2 retained-passive source-edge-family pre-measure inputs

## Claim

The fixed-base source edge-family map built from retained-passive coordinate
data lies in the retained-passive p.13 local source and has the expected
source-readback selected-entry residual-factor matrix readout, provided the
coordinate data has determinant-chart proofs and the stored `C` residual-factor
product has that selected-entry matrix form.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

Target name:

```lean
PaperEndpointFixedBaseRegularCoordinateSourceData.retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_sourceEdgeFamilyOfData
```

## Proof Basis

Instantiate the already-proved fixed-base pre-measure input bridge with
`Cedge := fun E => E` and

```text
sourceChart y =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    W B U₀ hU₀ (retainedData y).
```

The realization hypothesis of that bridge is discharged by
`paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceEdgeFamilyOfData_eq`.

## Nonclaims

This theorem does not construct or transport endpoint equivalences, transport
`edgeMatrix` or `sourceReadback`, prove fixed-base realization for the explicit
Case 2 transported datum, compare source priors or Jacobians, prove normal
crossings, pole order, or RLCT.

## Status

Sorry-free, focused build passed, and reviewed PASS by xhigh `Linnaeus` in
`review-a2-retained-passive-source-edge-family-premeasure-inputs.md`.
