# Review - A2 retained-passive inverse-Jacobian chart-side measurability wrapper

Reviewer: Franklin, xhigh read-only scout/reviewer.

## Verdict

PASS.

## Checks

- Source-measure orientation is unchanged: the raw inverse-Jacobian measure is
  `Measure.map rawChart ((m.restrict T).withDensity invJacDensity)`, and the
  residual handoff still proves its local-source restriction equals the direct
  determinant-chart pushforward before applying the generic residual-source
  socket.
- The determinant-chart residual hypotheses remain on `directChart` over
  `m.restrict S`; the wrapper does not assert raw-chart positivity.
- The `EFam` and `Cedge := id` types match the existing identity-source
  measurability lemma exactly.
- The declarations are placed after
  `measurableSet_residualSquareSum_pos_retainedPassiveP13Canonical_id`, so Lean
  can use the measurability theorem without moving established code.
- The finite-integral wrapper keeps local loss and density hypotheses explicit.

## Nonclaims Checked

This is an API cleanup that removes only the source-space residual positive-set
measurability field.  It does not prove determinant-chart residual positivity,
determinant-chart finite residual integrability, local loss bounds, density
bounds, source-rank coverage, original external prior transport, normal
crossings, pole order, or RLCT.

## Build

Reviewer did not run a build.  Controller-run focused build passed before this
review record; final commit gate runs the standard hygiene checks and axiom
probes.
