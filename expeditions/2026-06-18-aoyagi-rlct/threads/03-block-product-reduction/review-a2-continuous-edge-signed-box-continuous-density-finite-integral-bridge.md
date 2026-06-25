# Review - A2 continuous-edge signed-box continuous-density finite-integral bridge

Date: 2026-06-25.

Reviewer: xhigh `Sartre the 5th`.

## Verdict

Pass after a reproduction-note precision fix.  The Lean theorem and statement
card are sound at the stated scope.

## Finding

The reproduction's list of remaining analytic/source inputs omitted `0 < t`.
The reproduction now includes `0 < t` in that list.

## Scope Check

The Lean theorem derives only:

- source-stratum measurability from global `Continuous Cedge`, using
  `measurableSet_paperEndpointFixedBaseSourceRankStratum_of_continuous`;
- fixed-basis endpoint edge-matrix measurability from global `Continuous Cedge`,
  using `continuous_apply` and `continuous_linearMap_toMatrix`.

It then delegates to
`exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_continuousAt_pos_density`.

The theorem does not assert source-rank openness, does not derive anything from
only `ContinuousAt Cedge x₀`, and does not introduce a raw `Measurable Cedge`
API over continuous-linear-map spaces.  The measurable object is the
fixed-basis endpoint edge-matrix family.

The signed-box chart, source-density a.e.-measurability/nonnegativity/upper
bound, weighted pushforward, residual monomial lower bound, `0 < t`,
product-density continuity/positivity at `(x₀,0)`, and local regular-fiber loss
lower bound remain explicit hypotheses.

No chart construction, pushforward proof, density/Jacobian transport,
original-loss comparison, normal crossings, pole-order computation, or RLCT
extraction is proved.

## Verification

Reviewer verification: focused Lean check of
`DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean` from the `lean/`
project root succeeded.
