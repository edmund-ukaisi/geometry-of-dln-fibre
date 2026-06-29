# Statement Card - A2 Case 2 Passive Residual-Coordinate Product-Measure Pushforward

Status: sorry-free focused build; direct axiom probe passed; xhigh
feasibility and scope reviews passed.

Reproduction:

```text
reproduction-a2-case2-passive-residual-coordinate-product-measure-pushforward.md
```

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

## Claim

For the passive-parameter Case 2 source chart and the concrete product-domain
measure

```text
passiveMeasure.prod weightedBox,
```

the residual-coordinate pushforward of the chart-produced source measure is
the selected-entry chart-image measure, scaled by the total passive mass:

```text
passiveMeasure Set.univ •
  ((volume : Measure (center -> R)).restrict
    (CenterCoord.chartMap pivotNext '' CenterCoord.signedBoxSet Rres)).
```

The passive mass scalar is part of the theorem because `passiveMeasure` is
arbitrary.

## Lean

```text
measure_map_residualBlockCoordinateMap_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_eq_smul_restrict_chartMap_image
```

## Proved

- The chart-produced passive source measure can be composed with the residual
  coordinate map.
- Pointwise, the composed map is `CenterCoord.chartMap pivotNext` applied to
  the selected-entry coordinate `z.2`.
- Projecting `passiveMeasure.prod weightedBox` to the second coordinate gives
  `passiveMeasure Set.univ • weightedBox`.
- The selected-entry weighted signed-box chart-map theorem identifies the
  remaining pushforward with the Lebesgue restriction to the chart image.

## Assumed

- Arbitrary passive-domain measure `passiveMeasure : Measure eta`.
- Case 2 dimension hypotheses `hS`, `hcont`, and `hnext`.
- Endpoint equivalences `e` and `eNext`.
- Continuity of `A1passive`, `F2`, `A3passive`, `Ctop`, and `F3`.
- Pointwise determinant-unit hypotheses on `Ctop` and `A1passive`.
- `BorelSpace EdgeFamily` for the chart-produced map composition.

No source-rank hypotheses are assumed or concluded.

## Cited

Aoyagi pp. 10-13 motivate the passive p.13 source chart and residual readout.
The Lean proof itself is chart-produced measure bookkeeping using Mathlib
product projection and the already-proved selected-entry chart-map
pushforward.

## Deferred

- Determinant-chart Haar or raw/source Haar pushforward.
- Original DLN source-prior transport.
- Passive Jacobian/source-density accounting for an ambient prior.
- Source-rank coverage.
- Source-image equality, local inverse, or chart coverage of arbitrary source
  points.
- Normal crossings, pole order, and RLCT extraction.

## Build

Focused build passed from `lean/`:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
```

`git diff --check` passed.  `scripts/sorries` reports
`0 sorry, 0 #exit, 0 native_decide, 0 axiom`.

Direct axiom probe for the theorem reports
`[propext, Classical.choice, Quot.sound]`.

Independent xhigh read-only scouts `Faraday the 3rd` and `Dalton the 3rd`
confirmed the theorem shape, including the required scalar
`passiveMeasure Set.univ`.

## Nonclaims

This card proves only a residual-coordinate marginal of a chart-produced
product-domain measure.  It does not prove determinant-chart/source-prior
transport, source-rank coverage, a source-image theorem, Jacobian comparison,
normal crossings, pole order, or RLCT.
