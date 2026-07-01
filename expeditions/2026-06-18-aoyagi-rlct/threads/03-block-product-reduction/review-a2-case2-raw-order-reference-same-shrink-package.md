# Review - A2 Case 2 raw-order reference same-shrink package

Date: 2026-07-01.

Status: controller review PASS; xhigh Lean/API and source-boundary reviews
PASS after Lean landed.

## Checks

- The theorem must call the underlying local raw-order/source-chart package
  once and use the resulting `V` for every conclusion.
- The endpoint-to-raw image identity should use `AEMeasurable.map_map_of_aemeasurable`,
  because `topologyTupleEdgeRawOrder` is only needed locally on the determinant
  chart.
- The raw-density hypothesis must be relative to
  `case2PassiveThetaRawOrderReferenceImageMeasure ... V`.
- The domination conclusion must keep the target as the named image measure,
  not raw Haar or full determinant-chart volume.
- The `EdgeFamily` measurable and Borel hypotheses are needed for the
  source-chart map package.

## Boundary

This is an interface theorem: it prevents downstream users from accidentally
combining facts about different existential shrinks.  It does not add a new
mathematical comparison with Haar, original volume, or an original/source
prior.

The exact nonclaims to preserve are: no raw-Haar identification or raw-Haar
pushforward; no determinant-chart Haar domination or full determinant-chart
Haar target; no exact Haar transport, Haar normalization, or scalar
normalization; no full chart/image coverage; no p.13 source coverage; no
source-image or source-rank coverage; no original DLN source-prior or
original-volume transport; no Jacobian formula for `Y`; no bounded-density
construction or prior-density transport; no normal crossings, pole order, or
RLCT extraction.

## Verification

Focused elaboration, focused module build, full local `lake build DLNFibre`,
`lean/scripts/sorries`, `git diff --check`, and direct axiom probe passed.
The direct axiom probe for the new theorem reported only
`[propext, Classical.choice, Quot.sound]`.
