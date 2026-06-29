# Review: A2 retained-passive raw-order two-stage pushforward

## Source-scope review

Reviewer: `Boyle the 4th`, xhigh read-only source-scope review.

Status: PASS.

Findings:

- No source-scope overclaim.  The reproduction states that this is not a new
  Aoyagi source calculation and that the new content is local measurability
  needed to reassociate two `Measure.map` operations.
- The claim stays on the chart-produced restricted-sector measure
  `sourceMeasure.restrict V`.  It proves equality between chart-produced
  pushforwards, not raw determinant-chart Haar transport, source-product Haar,
  density/Jacobian transport, image equality, or coverage.
- The statement card and reproduction include the correct nonclaim boundary:
  no determinant-chart Haar transport, raw/source Haar theorem,
  external/original source-prior comparison, passive Jacobian formula, density
  identity, source-image equality, source-rank coverage, normal crossings, pole
  order, or RLCT extraction.
- Caveat: since no downstream intermediate-measure consumer is named yet, this
  checkpoint should be advertised as source-faithful API hardening, not as
  removing a source-prior or analytic frontier.

## Lean/API review

Reviewer: `Carver the 4th`, xhigh read-only Lean/API review.

Status: PASS.

Findings:

- The theorem is implementable using existing public APIs.  The private helper
  `retainedPassiveP13CanonicalSourceChart_aemeasurable` in
  `RetainedPassiveLocalJacobianMeasure.lean` should not be used; its short
  proof should be rebuilt from public continuity lemmas.
- Required measure-conclusion typeclasses are
  `MeasurableSpace` and `BorelSpace` on the raw-order `TopologyTuple` target,
  plus `MeasurableSpace` and `BorelSpace` on the edge-family target.  No
  Haar, sigma-finiteness, or finite-mass hypothesis is needed.
- The proof should use `ContinuousOn.aemeasurable₀` for `rawMap` on `V`, push
  `rawMap z in T` through `ae_map_iff`, prove `rawChart` a.e. measurable on
  the restricted target `T`, rewrite the target restriction by
  `Measure.restrict_eq_self_of_ae_mem`, and then use
  `AEMeasurable.map_map_of_aemeasurable`.
- Main traps: do not use `Measure.map_map`, do not assert global continuity of
  `rawMap` or `rawChart`, and do not use private Jacobian-module helpers as
  public API.

## Implementation check

The implemented theorem follows these review constraints:

- It proves `rawMap` local a.e. measurability by composing
  `continuous_topologyTuple` with the continuous retained data map and then
  the public `continuous_topologyTupleEdgeRawOrder_detChart_subtype`.
- It proves `rawChart` local a.e. measurability by reconstructing the public
  raw-order inverse, `ofTopologyTuple`, and direct retained-passive p.13 source
  chart continuity proof.
- It uses `AEMeasurable.map_map_of_aemeasurable`, not `Measure.map_map`.
- It adds no Haar, density, source-prior, coverage, normal-crossing, pole
  order, or RLCT hypothesis or conclusion.

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySourceMeasure`
and full `DLNFibre` build passed via `scripts/lb`; only pre-existing replay
warnings appeared.  `scripts/sorries`, `git diff --check`, touched Lean-file
forbidden-marker scan, and direct axiom probe passed.  The new theorem reports
`[propext, Classical.choice, Quot.sound]`.
