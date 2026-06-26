# Statement Card - A2 product-step determinant-chart image

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepMeasure.lean`

## Claim

Lean proves that the raw-order p. 13 product-step coordinate map is a bijection
from the raw determinant chart onto the raw-shaped target determinant chart.
Consequently, the weighted additive-Haar change-of-variables theorem can be
stated with target restricted to the determinant-chart predicate itself,
instead of the image set.

## Lean Names

```text
ProductReductionStepRawCoordinates.topologyTuple_mem_rawDetChartSet
productReductionStepRawCoordinatesOfTopologyTuple_of_topologyTuple
productReductionStepChartCoordinatesOfRawOrderTopologyTuple
productReductionStepChartCoordinatesOfRawOrderTopologyTuple_detChart
productReductionStepChartCoordinatesOfRawOrderTopologyTuple_rawOrder
ProductReductionStepChartCoordinates.rawOrderTopologyTuple_mem_rawDetChartSet
mapsTo_productReductionStepTopologyTupleToChartRawOrder_detChart
surjOn_productReductionStepTopologyTupleToChartRawOrder_detChart
bijOn_productReductionStepTopologyTupleToChartRawOrder_detChart
image_productReductionStepTopologyTupleToChartRawOrder_detChart
map_productReductionStepRawOrder_restrict_detChart_withDensity_absDet_eq_restrict_detChart
```

## Inputs

- real finite matrix coordinates;
- `[Fintype rho] [DecidableEq rho]`;
- `[Finite pi]` where injectivity is used;
- `[Fintype mu]`;
- `[Finite nu]` for image/bijection bookkeeping;
- for the strengthened Haar theorem, `[Fintype pi] [Fintype nu]`, a Borel
  measurable structure, an additive Haar measure `m`, and
  `NullMeasurableSet (productReductionStepRawDetChartSet rho pi mu nu) m`.

## Not Proved

This is not original DLN source/prior measure transport, not unweighted
pushforward, not finite source coverage, not a normal-crossing certificate,
and not an RLCT or pole-order theorem.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepMeasure
```

Verified on 2026-06-26 with the focused module build passing.
