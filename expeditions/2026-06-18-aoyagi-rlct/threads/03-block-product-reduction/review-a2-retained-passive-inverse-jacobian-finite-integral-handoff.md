# Review - A2 retained-passive inverse-Jacobian finite-integral handoff

Reviewer: Huygens, xhigh read-only review.

## Verdict

PASS after documentation correction.

## Checks

- The source measure is the intended raw-order retained-passive p.13 source
  measure with inverse-Jacobian density:
  `Measure.map rawChart ((m.restrict T).withDensity invJacDensity)`.
- The proof uses
  `residualSourceHypotheses_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian`
  to obtain local residual positivity and `residualNegPowerIntegrableOn` before
  calling the retained-passive p.13 local finite-integral socket.
- The determinant-chart residual positivity and finite residual integral are
  correctly supplied through the direct chart over `m.restrict S`; the raw-order
  source measure is only introduced through the inverse-Jacobian handoff.
- The `[SFinite m]` requirement supports the downstream product/restriction
  finite-integral socket; it is not hidden or synthesized.
- The call to the local socket uses `Cedge := fun E => E`, the base identity by
  `rfl`, and `continuous_id` for continuity, matching the identity
  retained-passive local source.

## Correction

The first review pass found one documentation overstatement: the theorem also
assumes source-space residual positive-set measurability, while the initial
statement card grouped it with determinant-chart residual facts.  The card,
reproduction note, and Lean docstring now name that measurability input
separately.

## Nonclaims Checked

No determinant-chart residual positivity/integrability proof, no selected-entry
residual integrability, no source-rank coverage, no original external
source-prior transport, no normal crossings, no pole order, and no RLCT are
claimed.

## Read-Only Hygiene

The reviewer did not run a build.  Controller-run build, sorry scan, diff
check, forbidden-marker search, and axiom probe gate the committed state.
