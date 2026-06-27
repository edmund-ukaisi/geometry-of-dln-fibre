# Statement Card: A2 retained-passive composed weighted COV

## Claim

The retained-passive weighted raw-order change-of-variables theorem can be
composed with any downstream map `ψ`, provided `ψ` is a.e.-measurable on the
raw-order target-chart measure.  A specialization reads the composed map as the
retained-passive coordinate-to-edge-family map via
`edgeFamilyOfRawOrderTuple_topologyTupleEdgeRawOrder`.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesMeasure.lean
```

Intended names:

```text
map_comp_topologyTupleEdgeRawOrder_withDensity_absDet_eq_map_restrict_rawSourceChart
map_topologyTupleEdgeMatrix_withDensity_absDet_eq_map_edgeFamilyOfRawOrderTuple
map_comp_topologyTupleEdgeRawOrder_restrict_detChart_eq_map_invJac_of_aemeasurable
map_topologyTupleEdgeMatrix_restrict_detChart_eq_map_edgeFamily_invJac_of_aemeasurable
```

## Hypotheses

Generic theorem:

- `m` is an additive Haar measure on retained-passive tuple coordinates;
- `topologyTupleDetChartSet` is null-measurable for `m`;
- `ψ` is a.e.-measurable with respect to
  `m.restrict topologyTupleRawOrderSourceRecursiveDetChartSet`.

Edge-family specialization:

- the same Haar and null-measurability hypotheses;
- `edgeFamilyOfRawOrderTuple` is a.e.-measurable with respect to the raw-order
  target-chart measure.

Inverse-density companion:

- the hypotheses of
  `map_topologyTupleEdgeRawOrder_restrict_detChart_eq_withDensity_inverseJacobian_of_aemeasurable`;
- downstream a.e.-measurability on the unweighted raw-order target-chart
  measure, which is lifted to the inverse-density target by absolute
  continuity.

## Nonclaims

This checkpoint does not prove:

- determinant-density continuity or measurability;
- inverse-density measurability;
- a fixed-base p.13 source-chart realization theorem;
- source-prior density identity;
- original DLN source pushforward;
- local-source coverage;
- normal crossings, pole order, or RLCT.

## Verification Plan

1. Build `DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesMeasure`.
2. Ask an xhigh reviewer to audit that the bridge is only measure-map
   composition.
3. Run full `DLNFibre`, `scripts/sorries`, and `git diff --check` before
   committing.
