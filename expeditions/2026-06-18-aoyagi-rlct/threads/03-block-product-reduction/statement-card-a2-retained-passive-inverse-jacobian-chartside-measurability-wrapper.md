# Statement Card - A2 retained-passive inverse-Jacobian chart-side measurability wrapper

## Claim

For the raw-order retained-passive p.13 inverse-Jacobian source measure, the
residual-source and finite-integral handoffs can be stated from determinant
chart-side residual hypotheses only: the source-space residual positive-set
measurability is discharged by the existing identity-source measurability
lemma.

## Source / Proof Basis

Aoyagi PDF pp. 11-13 for the retained-passive p.13 source-coordinate
construction.  This is finite source-coordinate measurability plus wrapper
composition, not an analytic zero-locus or normal-crossing argument.

Lean dependencies:

```text
measurableSet_residualSquareSum_pos_retainedPassiveP13Canonical_id
residualSourceHypotheses_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian
```

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalJacobianMeasure.lean
```

Declarations:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_chartSide
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_chartSide
```

## Nonclaims

No proof of determinant-chart residual positivity or finite residual integral;
no local loss or density-bound proof; no selected-entry residual
integrability, source-rank coverage, original external DLN prior transport,
normal crossings, pole order, or RLCT.

## Verification Plan

Run focused build of `DLNFibre.DLN.Aoyagi.RetainedPassiveLocalJacobianMeasure`,
then `scripts/sorries`, `git diff --check`, touched Lean-file forbidden-marker
search, direct axiom probes, and xhigh review.

## Verification Result

Focused build, `scripts/sorries`, `git diff --check`, touched Lean-file
forbidden-marker search, and direct axiom probes passed; both new declarations
report only `[propext, Classical.choice, Quot.sound]`.  Xhigh read-only review
by Franklin passed with the placement caution that the wrappers must occur after
`measurableSet_residualSquareSum_pos_retainedPassiveP13Canonical_id`; the
implemented declarations do.
