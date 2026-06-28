# Statement card: A2 retained-passive canonical residual measurability handoff

## Lean names

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalJacobianMeasure.lean
```

```text
measurableSet_residualSquareSum_pos_retainedPassiveP13Canonical_id
residualSourceHypotheses_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet_of_chartSide
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet_of_chartSide
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet_continuousAt_pos_density_of_chartSide
```

## Content

The measurability lemma proves that the source-side positive-residual set for
the canonical identity retained-passive source is measurable.  It combines:

```text
continuous_id
continuous_paperEndpointFixedBaseRetainedPassiveP13EdgeMatrix_of_continuous
measurable_paperEndpointFixedBaseResidualBlockCoordinateMap_of_measurable_edgeMatrix
measurableSet_residualSquareSum_pos_of_measurable
```

The residual handoff wrapper removes only the source-side positive-set
measurability argument from the existing canonical product-density residual
handoff.

The fixed-radius and continuous-density finite-integral wrappers remove the
same source-side measurability argument from the previous canonical
finite-integral front ends.  The chart-side residual positivity, chart-side
finite residual integral, local loss lower bound, and density hypotheses remain
explicit.

## Verification

Focused `RetainedPassiveLocalJacobianMeasure` build passed.  Full `DLNFibre`
build passed with pre-existing warning noise.  `scripts/sorries`,
`git diff --check`, and the touched-file forbidden-marker search passed.

Xhigh review by `Hegel the 2nd` passed.

## Nonclaims

No chart-side residual positivity, residual zero-locus nullity, residual
integrability, monomial lower bound, signed-box density identification,
original prior transport, normal-crossing production, pole-order theorem, or
RLCT theorem is claimed.
