# Statement Card - A2 retained-passive direct source chart inverse-Jacobian measure

## Claim

The fixed-base retained-passive p.13 source measure obtained directly from
determinant-chart coordinates equals the public raw-order p.13 source-chart
measure with the inverse-Jacobian density.

## Source / Proof Basis

Aoyagi PDF pp. 11-13 for the p.13 retained-passive source-coordinate
construction.  The proof is a local finite-dimensional change-of-variables
handoff already formalised in the retained-passive coordinate infrastructure,
plus the pointwise raw-order/direct source-chart identity.

Lean dependencies:

```text
map_comp_topologyTupleEdgeRawOrder_restrict_detChart_eq_map_invJac
topologyTupleEdgeRawOrderInverseJacobianDensity
paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_eq_sourceEdgeFamilyOfData
retainedPassiveP13CanonicalSourceChart_aemeasurable
nullMeasurableSet_topologyTupleDetChartSet
Measure.map_congr
ae_restrict_mem₀
```

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalJacobianMeasure.lean
```

Expected declaration:

```text
measure_map_paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_restrict_detChart_eq_map_rawOrderSourceChart_withDensity_inverseJacobian
```

## Nonclaims

No original external DLN prior identification, no source-prior theorem beyond
this retained-passive chart layer, no source-rank coverage, no selected-entry
residual positivity/integrability, no normal crossings, no pole order, and no
RLCT extraction.

Retained hypotheses include finite-dimensional fixed-base data, measurable and
Borel structures on the topology-tuple and edge-family spaces, and Haar measure
on the topology-tuple coordinate space.

## Verification Plan

Run focused build of `DLNFibre.DLN.Aoyagi.RetainedPassiveLocalJacobianMeasure`,
then `scripts/sorries`, `git diff --check`, touched-file forbidden-marker
search, direct axiom probe for the new declaration, and xhigh review.
