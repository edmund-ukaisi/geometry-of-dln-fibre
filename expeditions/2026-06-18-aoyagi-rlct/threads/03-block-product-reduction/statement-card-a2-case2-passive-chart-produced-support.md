# Statement Card - A2 Case 2 Passive Chart-Produced Support

Status: sorry-free focused build; direct axiom probe passed; xhigh review PASS.

Reproduction:

```text
reproduction-a2-case2-passive-chart-produced-support.md
```

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

## Claim

For the passive-parameter Case 2 source chart on
`eta x (center -> R)`, any chart-produced source measure is supported on the
retained-passive p.13 local source when the source chart is a.e. measurable.
If the successor source-rank equation holds a.e. for that passive-domain
measure, then the same pushforward measure is also supported on the named
source-rank stratum.

## Lean

```text
measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_restrict_retainedPassiveP13LocalSource_eq_self
measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_restrict_sourceRankStratum_eq_self
```

## Proved

- `Measure.map sourceChart sourceMeasure` restricts to the retained-passive
  p.13 local source as itself.
- Under `hprod`, `hr0`, and an a.e. successor-rank hypothesis, the same
  chart-produced measure restricts to the source-rank stratum as itself.
- The source measure is arbitrary on the passive-domain product type; the
  theorem does not construct a product measure or a source prior.
- Measurability of `sourceChart` is an explicit `AEMeasurable` hypothesis.

## Assumed

- Endpoint equivalences `e` and residual-column equivalence `eNext`.
- Case 2 dimension hypotheses `hS`, `hcont`, and `hnext`.
- Passive field families indexed by an arbitrary measurable type `eta`.
- Unit hypotheses `forall theta, IsUnit (Ctop theta).det` and
  `forall theta p, IsUnit ((A1passive theta p).det)`.
- A.e. measurability of the passive source chart for the chosen
  `sourceMeasure`.
- For source-rank support only: `hprod`, `hr0`, and an a.e. successor-rank
  equation.

## Cited

Aoyagi pp. 10-13 motivate the retained-passive block/product chart and the
p.13 residual product display.  The Lean proof itself is support bookkeeping
from already-landed pointwise passive local-source/source-rank lemmas and
generic measure restriction lemmas.

## Deferred

- Construction of a concrete passive product source measure.
- Continuity or measurability of the passive source chart from passive field
  continuity.
- Source-rank coverage of arbitrary nearby source points.
- Source-image equality or local coverage for the passive-selected-entry
  sector.
- Determinant-chart pushforward, passive Jacobian, bounded-unit density
  accounting, or original source-prior transport.
- Normal crossings, pole order, and RLCT extraction.

## Build

Focused build passed from `lean/`:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
```

Direct axiom probes for both theorem names report
`[propext, Classical.choice, Quot.sound]`.
Independent xhigh review by `Peirce the 3rd` passed with no findings; see
`review-a2-case2-passive-chart-produced-support.md`.

## Nonclaims

This card does not prove a product-measure construction, source-rank
coverage, source-image equality, determinant-chart Haar pushforward, raw-Haar
transport, source-prior transport, Jacobian transport, normal crossings, pole
order, or RLCT.
