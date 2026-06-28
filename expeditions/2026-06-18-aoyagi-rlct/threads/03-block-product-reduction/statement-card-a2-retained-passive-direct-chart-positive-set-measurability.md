# Statement card - A2 retained-passive direct-chart positive-set measurability

## Declaration

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  measurableSet_residualSquareSum_pos_retainedPassiveP13Canonical_directChart
```

## File

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalJacobianMeasure.lean
```

## Statement

For the canonical retained-passive p.13 direct chart

```text
z |-> paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
        W B U0 hU0 (ofTopologyTuple z),
```

the positive set of the fixed-base residual square-sum is measurable:

```text
{z | 0 < aoyagiCoordinateSquareSum
  (paperEndpointFixedBaseResidualBlockCoordinateMap W B U0 hU0 id
    (directChart z))}.
```

The theorem carries the ambient `MeasurableSpace` and `BorelSpace` assumptions
on the retained-passive `TopologyTuple`.

## Proof Basis

The proof uses the ambient retained-passive readout identity

```text
paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceEdgeFamilyOfData_eq
```

to rewrite the direct chart's fixed-basis edge matrices to
`(ofTopologyTuple z).edgeMatrix`.  Those edge matrices are measurable because
the retained-passive solved `A1` and `A3` blocks are assembled from finite
matrix operations and global real matrix inverse, which is Borel-measurable.
The residual-coordinate API then gives measurable residual coordinates, and
the positive square-sum set follows from finite-coordinate measurability.

## Consumers Updated

The helper removes the explicit target positive-set measurability hypothesis
from:

```text
retainedPassiveP13Canonical_detChart_residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_selectedEntrySignedBox_map
residualSourceHypotheses_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_case2EndpointTransport_selectedEntrySignedBox_map
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_case2EndpointTransport_selectedEntrySignedBox_map
```

## Boundary

This proves only finite coordinate measurability of a positive set.  It does
not prove residual positivity, residual integrability, determinant-chart
pushforward, chart coverage, original external source-prior transport, local
loss or density bounds, source-rank coverage, normal crossings, pole order, or
RLCT extraction.

## Verification

Focused builds passed:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalJacobianMeasure
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
```
