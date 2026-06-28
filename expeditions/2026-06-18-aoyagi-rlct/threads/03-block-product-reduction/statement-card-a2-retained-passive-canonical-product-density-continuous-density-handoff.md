# Statement card: A2 retained-passive canonical product-density continuous-density handoff

## Lean target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalJacobianMeasure.lean
```

## Lean name

```text
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet_continuousAt_pos_density
```

## Content

The theorem specializes the canonical product-density finite-integral handoff
by deriving the two local density-bound hypotheses from:

```text
ContinuousAt density (base, 0)
0 < density (base, 0)
```

and shrinking the regular-coordinate radius from `Rmax` to an output `R <=
Rmax`.

The chart-side residual positive-set measurability, chart-side residual
positivity, chart-side finite residual integral, and local loss lower bound
remain hypotheses.

The proof applies the generic positive-continuous density-bounds helper on the
retained-passive local source and restricts the loss lower bound along
`Metric.ball 0 R <= Metric.ball 0 Rmax`.

## Verification

Focused `RetainedPassiveLocalJacobianMeasure` build passed.  Full `DLNFibre`
build passed with pre-existing warning noise.  `scripts/sorries`,
`git diff --check`, and the touched-file forbidden-marker search passed.

Xhigh review by `Godel the 2nd` passed.

## Nonclaims

No original-source prior, selected-entry signed-box density identification,
monomial residual lower bound, normal-crossing production, pole-order theorem,
or RLCT theorem is claimed.
