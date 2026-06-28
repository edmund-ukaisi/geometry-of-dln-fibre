# Review: A2 retained-passive canonical residual measurability handoff

Reviewer: xhigh `Hegel the 2nd`.

Verdict: PASS.

## Scope

The review checked these Lean names:

```text
measurableSet_residualSquareSum_pos_retainedPassiveP13Canonical_id
residualSourceHypotheses_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet_of_chartSide
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet_of_chartSide
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet_continuousAt_pos_density_of_chartSide
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalJacobianMeasure.lean
```

and the matching reproduction note and statement card.

## Checks

The reviewer ran the focused build for
`DLNFibre.DLN.Aoyagi.RetainedPassiveLocalJacobianMeasure`; it passed, with only
unrelated replayed warning noise from `ProductReductionStepRegularDensity.lean`.

The canonical measurability lemma is scoped to `Cedge = id` and uses only the
finite fixed-base coordinate chain: `continuous_id`, fixed-base edge-matrix
continuity, residual block measurability, and measurable finite square-sum
positive set.

The three wrappers remove only the source-side residual positive-set
measurability hypothesis.  Chart-side a.e. residual positivity and finite
residual integral remain explicit.  Each wrapper supplies only the generated
`hpos_meas` before delegating to the existing canonical handoff.

The notes keep the nonclaim boundary: no zero-locus nullity, residual
integrability, monomial lower bound, signed-box density, original prior
transport, normal crossings, pole order, or RLCT claim.
