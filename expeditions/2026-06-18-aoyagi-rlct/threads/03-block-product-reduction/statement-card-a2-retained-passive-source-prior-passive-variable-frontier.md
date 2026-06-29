# Statement Card - A2 Retained-Passive Source-Prior Passive-Variable Frontier

Status: reproduced frontier; no Lean theorem yet.

Reproduction:

```text
reproduction-a2-retained-passive-source-prior-passive-variable-frontier.md
```

Review:

```text
review-a2-retained-passive-source-prior-passive-variable-frontier.md
```

Scout inputs:

```text
reorientation-a2-source-frontier-2026-06-29.md
```

## Claim

The current Case 2 selected-entry signed-box source measure is a
chart-produced reduced-section measure.  It cannot by itself remove the
determinant-chart pushforward hypothesis

```text
m.restrict Sdet = Measure.map chart weightedBox
```

and it cannot be identified with an original/external DLN source prior.

To remove that field, the retained-passive p.13 source construction must add
the passive variables suppressed by the reduced section, then prove a source
map, local inverse, image or coverage theorem, and Jacobian/source-density
transport.

## Source Basis

Aoyagi pp. 10-13 explicitly support the finite block substitutions

```text
F2 = -A1^{-1} A2
F3 = -A3 A1^{-1}
C4 = -A3 A1^{-1} A2 + A4
```

and the p.13 product-difference display

```text
[ C1 - I        -F2
  -F3    prod C^(s) - F3 F2 ].
```

They do not state selected-entry signed-box coverage of the determinant chart,
source-rank image equality, raw/source Haar pushforward, or original
source-prior transport.

## Existing Lean Infrastructure

Relevant already-proved chart-layer infrastructure:

```text
productReductionStepRawOrderJacobianAbsDet
productReductionStepRawOrderInverseJacobianDensity
map_productReductionStepRawOrder_restrict_detChart_eq_withDensity_inverseJacobian

topologyTupleEdgeRawOrderFDerivAbsDet
topologyTupleEdgeRawOrderInverseJacobianDensity
map_topologyTupleEdgeRawOrder_restrict_detChart_eq_withDensity_inverseJacobian
measure_map_paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_restrict_detChart_eq_map_rawOrderSourceChart_withDensity_inverseJacobian

paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamily_homeomorph
image_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_eq_sourceEdgeFamilySet
paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceEdgeFamily_homeomorph
```

These prove retained-passive chart change-of-variables and reduced image
facts.  They do not prove the external/source-prior theorem.

## Next Acceptable Lean Payoff

The next Lean theorem should remove an actual supplied field.  The following
names are schematic placeholders, not implementation-ready declarations:

```text
map_retainedPassiveFullCoordinateSourceChart_eq_rawOrderMeasure_withDensity
map_retainedPassivePassiveSelectedEntryChart_eq_sectorMeasure
exists_open_case2EndpointTransport_sourceRankStratum_subset_selectedEntryPassiveImage
```

Before implementation, sharpen one of these into an actual statement with
explicit coordinate domain, source map, local inverse or image theorem, source
and target measures, local neighborhood, pivot-sector, and rank hypotheses.

A theorem that still assumes `m.restrict Sdet = Measure.map chart weightedBox`,
assumes a source-prior equality, or defines the source measure to be the target
measure is not progress at this frontier.

## Nonclaims

No source-prior transport, selected-entry image coverage, exact-rank openness,
normal crossings, pole order, or RLCT extraction is proved by this card.  The
normal-crossing-to-RLCT extraction remains the cited analytic boundary.
