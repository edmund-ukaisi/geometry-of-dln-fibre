# Statement Card - A2 retained-passive inverse-Jacobian residual-source handoff

## Claim

The retained-passive raw-order source measure with inverse-Jacobian density
satisfies the p.13 residual-source hypotheses once the direct determinant-chart
pullback has a.e. positive residual square-sum and finite residual
negative-power integral.

## Source / Proof Basis

Aoyagi PDF pp. 11-13 for the retained-passive p.13 source-coordinate
construction.  The proof is measure transport and residual-source bookkeeping;
it uses the already formalised retained-passive raw-order inverse-Jacobian
change of variables.

Lean dependencies:

```text
measure_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_restrict_retainedPassiveP13LocalSource_eq_self
measure_map_paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_restrict_detChart_eq_map_rawOrderSourceChart_withDensity_inverseJacobian
retainedPassiveP13CanonicalSourceChart_aemeasurable
paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13RawOrderSourceChart_eq
nullMeasurableSet_topologyTupleRawOrderSourceRecursiveDetChartSet
nullMeasurableSet_topologyTupleDetChartSet
continuous_paperEndpointFixedBaseRetainedPassiveP13SourceChart
residualSourceHypotheses_of_measure_map
withDensity_absolutelyContinuous
ae_map_iff
Measure.restrict_eq_self_of_ae_mem
```

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalJacobianMeasure.lean
```

Expected declaration:

```text
measure_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_restrict_retainedPassiveP13LocalSource_eq_self
residualSourceHypotheses_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian
```

## Nonclaims

No proof of the chart-side residual hypotheses, no source-rank coverage, no
selected-entry residual positivity, no normal crossings, no pole order, no RLCT
extraction, and no identification with an original external DLN prior.

Retained hypotheses include finite-dimensional fixed-base data,
measurable/Borel structures on topology tuples and edge families, Haar measure
on topology tuples, source-side positive-set measurability, and direct
chart-side residual positivity/integrability.

## Verification Plan

Run focused build of `DLNFibre.DLN.Aoyagi.RetainedPassiveLocalJacobianMeasure`,
then `scripts/sorries`, `git diff --check`, touched-file forbidden-marker
search, direct axiom probe for the new declaration, and xhigh review.

## Verification Result

Focused build, `scripts/sorries`, `git diff --check`, touched Lean-file
forbidden-marker search, direct axiom probes, and xhigh review passed.  Review:
`review-a2-retained-passive-inverse-jacobian-residual-source-handoff.md`.
