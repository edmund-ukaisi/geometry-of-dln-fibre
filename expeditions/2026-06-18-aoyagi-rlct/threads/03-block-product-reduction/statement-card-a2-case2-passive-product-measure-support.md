# Statement Card - A2 Case 2 Passive Product-Measure Support

Status: sorry-free focused build; direct axiom probe passed; xhigh review PASS.

Reproduction:

```text
reproduction-a2-case2-passive-product-measure-support.md
```

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

## Claim

For the passive-parameter Case 2 source chart, the concrete passive-domain
product measure

```text
passiveMeasure.prod
  (signedBox.withDensity selectedEntrySourceDensity)
```

has a chart-produced pushforward supported on the retained-passive p.13 local
source when the passive fields are continuous and the determinant-chart unit
hypotheses hold.  Under an additional explicit a.e. successor-rank equation,
the same chart-produced pushforward is supported on the named source-rank
stratum.

## Lean

```text
case2PassiveDomainProductMeasure_eq_prod_withDensity_sourceDensity
measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_restrict_retainedPassiveP13LocalSource_eq_self
measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_restrict_sourceRankStratum_eq_self
```

## Proved

- The passive-domain product measure with selected-entry density on the second
  factor rewrites as a density over `passiveMeasure.prod signedBox`.
- The concrete chart-produced source measure restricts to the retained-passive
  p.13 local source as itself.
- With `hprod`, `hr0`, and an explicit a.e. successor-rank hypothesis on the
  concrete source-domain measure, it also restricts to the source-rank stratum
  as itself.
- A.e. measurability of the source chart is derived from the passive
  source-chart continuity theorem.

## Assumed

- Arbitrary passive-domain measure `passiveMeasure : Measure eta`.
- Case 2 dimension hypotheses `hS`, `hcont`, and `hnext`.
- Endpoint equivalences `e` and `eNext`.
- Continuity of `A1passive`, `F2`, `A3passive`, `Ctop`, and `F3`.
- Pointwise unit hypotheses `forall theta, IsUnit (Ctop theta).det` and
  `forall theta p, IsUnit ((A1passive theta p).det)`.
- For source-rank support only: `hprod`, `hr0`, and an a.e. successor-rank
  equation on `passiveMeasure.prod weightedBox`.
- `BorelSpace EdgeFamily` for `Continuous.aemeasurable`.

## Cited

Aoyagi pp. 10-13 motivate the retained-passive source chart and the selected-
entry p.13 density.  The Lean proof itself is measure bookkeeping:
Mathlib's product-with-density identity, continuity-to-a.e.-measurability, and
the already-proved arbitrary passive chart-produced support theorems.

## Deferred

- Source-rank coverage or proof of the successor-rank equation.
- Source-image equality or local inverse/coverage for arbitrary source points.
- Determinant-chart pushforward.
- Passive Jacobian/source-density accounting for an ambient source prior.
- Original source-prior transport.
- Normal crossings, pole order, and RLCT extraction.

## Build

Focused build passed from `lean/`:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
```

`git diff --check` passed.  `scripts/sorries` reports
`0 sorry, 0 #exit, 0 native_decide, 0 axiom`.

Direct axiom probes for all three theorem names report
`[propext, Classical.choice, Quot.sound]`.
Independent xhigh scouting/review by `Lorentz the 3rd` and
`Averroes the 3rd` passed; see
`review-a2-case2-passive-product-measure-support.md`.

## Nonclaims

This card does not prove source-prior transport, determinant-chart Haar
pushforward, raw-Haar transport, source-rank coverage, source-image equality,
Jacobian transport, normal crossings, pole order, or RLCT.
