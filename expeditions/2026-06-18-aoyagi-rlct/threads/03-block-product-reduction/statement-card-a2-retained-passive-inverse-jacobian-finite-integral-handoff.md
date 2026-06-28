# Statement Card - A2 retained-passive inverse-Jacobian finite-integral handoff

## Claim

For the raw-order retained-passive p.13 source measure with inverse-Jacobian
density, the p.13 regular-coordinate local integral is finite once the
source-space residual positive set is measurable, the direct determinant-chart
pullback satisfies residual positivity and finite residual negative-power
integrability, and the local loss and density bounds hold near the fixed base
source.

## Source / Proof Basis

Aoyagi PDF pp. 11-13 for the retained-passive p.13 source-coordinate
construction.  The proof is measure transport plus the already formalised
retained-passive p.13 local finite-integral socket.

Lean dependencies:

```text
residualSourceHypotheses_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource
continuous_id
```

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalJacobianMeasure.lean
```

Declaration:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian
```

## Nonclaims

No proof of source-space residual positive-set measurability, determinant-chart
residual positivity, or finite residual integral; no selected-entry residual
integrability, source-rank coverage, original external DLN prior transport,
normal crossings, pole order, or RLCT.

## Verification Plan

Run focused build of `DLNFibre.DLN.Aoyagi.RetainedPassiveLocalJacobianMeasure`,
then `scripts/sorries`, `git diff --check`, touched Lean-file forbidden-marker
search, direct axiom probe, and xhigh review.

## Verification Result

Focused build, `scripts/sorries`, `git diff --check`, touched Lean-file
forbidden-marker search, direct axiom probe, and xhigh review passed after
documentation separated the source-space measurability input from the
determinant-chart residual hypotheses.  Review:
`review-a2-retained-passive-inverse-jacobian-finite-integral-handoff.md`.
