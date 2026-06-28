# Review - A2 retained-passive direct source chart inverse-Jacobian measure

Reviewer: Mencius, xhigh read-only.

Verdict: PASS.

## Findings

- The theorem states the intended measure identity:
  `Measure.map directChart (m.restrict S)` equals
  `Measure.map rawChart ((m.restrict T).withDensity ...)`, with the density
  `topologyTupleEdgeRawOrderInverseJacobianDensity` on the raw-order target
  side.
- No forward/inverse Jacobian reversal was found.  The density is the
  target-side inverse density `|det Df(f^-1 y)|^-1`, and the change-of-
  variables theorem used by the proof has the same target-side inverse-density
  conclusion.
- The proof is faithful to the reproduction: raw-chart a.e. measurability is
  supplied by `retainedPassiveP13CanonicalSourceChart_aemeasurable`; the a.e.
  direct/raw source-chart equality uses
  `paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_eq_sourceEdgeFamilyOfData`
  on `topologyTupleDetChartSet`; the change-of-variables step applies
  `map_comp_topologyTupleEdgeRawOrder_restrict_detChart_eq_map_invJac` with
  `psi = rawChart`; and the final comparison uses `Measure.map_congr`.
- The notes correctly bound the result as a retained-passive chart-layer
  change-of-variables theorem only.  They do not claim original external prior
  transport, source-rank coverage, residual positivity/integrability, normal
  crossings, pole order, or RLCT extraction.

## Checks

The controller ran the focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveLocalJacobianMeasure`, `scripts/sorries`,
`git diff --check`, touched Lean-file forbidden-marker search, and direct axiom
probe.  The theorem reports only `[propext, Classical.choice, Quot.sound]`.
The reviewer also ran focused elaboration, `git diff --check`, and a
placeholder scan.  The optional spelling nit `ae_restrict_mem0` was corrected
to `ae_restrict_mem₀`.
