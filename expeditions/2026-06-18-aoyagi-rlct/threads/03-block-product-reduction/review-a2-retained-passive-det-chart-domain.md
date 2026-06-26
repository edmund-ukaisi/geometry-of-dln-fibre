# Review - A2 Retained-Passive Determinant-Chart Domain

Date: 2026-06-26.

Reviewer: xhigh read-only reviewer `Poincare the 3rd`.

Verdict: survived.

## Target

Lean and docs for the retained-passive determinant-domain rung:

```text
RetainedPassiveNonredundantCoordinateData.detChart
RetainedPassiveNonredundantCoordinateData.detChartSet
RetainedPassiveNonredundantCoordinateData.edgeMatrix_readbacks_eq_targets_of_detChart
RetainedPassiveNonredundantCoordinateData.edgeMatrix_ext_of_detChart
RetainedPassiveNonredundantCoordinateData.injOn_edgeMatrix_detChartSet
RetainedPassiveNonredundantCoordinateData.TopologyTuple
RetainedPassiveNonredundantCoordinateData.isOpen_detChartSet
RetainedPassiveNonredundantCoordinateData.detChartSet_mem_nhds
```

Files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
lean/DLNFibre.lean
reproduction-a2-retained-passive-det-chart-domain.md
statement-card-a2-retained-passive-det-chart-domain.md
```

## Checks

The reviewer found that `detChart` is exactly the active `Ctop`
determinant-unit condition plus passive `A1passive` determinant-unit
conditions.  For `M=0`, the passive clause is vacuous and only
`IsUnit data.Ctop.det` remains.

The domain wrappers are faithful: the readback theorem unpacks `detChart` into
the old passive `A1` and `Ctop` hypotheses, the extensionality wrapper does
the same for both records, and `injOn_edgeMatrix_detChartSet` states only
`Set.InjOn` on the determinant-domain set.

The topology tuple matches the field order
`(A1passive,F2,A3passive,C,Ctop,F3)`.  The openness theorem proves only
coordinate-domain openness from determinant continuity and the open unit locus
under the stated topological-ring/open-units assumptions.  It does not prove
continuity of `edgeMatrix` or image openness.

The added `DLNFibre.lean` import follows the local aggregator convention of
adding new imports at the end.

The docs avoid the listed overclaims: image openness, continuity of
`edgeMatrix`, source-rank coverage, source/image equality, measure/Jacobian
transport, normal crossings, pole order, and RLCT.

## Verification

The reviewer ran the focused Lean check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
```

It completed successfully.
