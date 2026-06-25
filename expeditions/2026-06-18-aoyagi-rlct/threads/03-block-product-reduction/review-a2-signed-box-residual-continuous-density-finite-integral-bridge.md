# Review - A2 signed-box residual continuous-density finite-integral bridge

Date: 2026-06-25.

Reviewer: xhigh `Aristotle the 5th`.

## Verdict

Pass after a statement-card precision fix.  The Lean theorem is sound
composition of existing residual-source and continuous-density local-measure
bridges.

## Finding

The statement card said "radius-shrinking finite-integral conclusion" but did
not explicitly record the formal output `0 < R` and `R ≤ Rmax`.  The card now
states that the produced radius satisfies both inequalities.

## Scope Check

The Lean proof only calls
`residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_edgeMatrix`
and then feeds the resulting residual positivity and residual negative-power
integrability into
`exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_continuousAt_pos_density`.

The assumptions remain explicit: source-stratum measurability, fixed-basis
edge-matrix measurability, signed-box chart a.e.-measurability,
source-density a.e.-measurability/nonnegativity/upper bound, weighted
pushforward, residual monomial lower bound, `0 < t`, product-density
continuity/positivity at `(x₀,0)`, and the local regular-fiber loss lower
bound.

The theorem does not construct a chart, prove a pushforward identity, transport
density or Jacobian factors, compare original `lossDLN`, produce normal
crossings, compute pole order, or extract an RLCT.

## Verification

Reviewer verification: focused Lean check of
`DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean` from the `lean/`
project root succeeded.
