# Review - A2 signed-box residual source finite-integral bridge

Date: 2026-06-25.

Reviewer: xhigh `Russell the 5th`.

## Verdict

Pass after documentation fixes.  The Lean theorem is sound measure/integrability
plumbing.

## Findings

- The statement card omitted explicit assumptions `0 < t`,
  source-density a.e.-measurability, and source-density a.e. nonnegativity.
  The card now lists these assumptions.
- The reproduction said the signed-box source constructor works under
  `t >= 0`, but the composed p.13 handoff requires `0 < t`.  The reproduction
  now records that the residual-source constructor is applied with
  `t >= 0` derived from `0 < t`.

## Scope Check

The theorem explicitly assumes source-stratum measurability, fixed-basis
edge-matrix measurability, signed-box chart a.e.-measurability,
source-density a.e.-measurability, weighted pushforward, residual monomial
lower bound, source-density a.e. nonnegativity, source-density monomial upper
bound, and local regular-fiber loss/density bounds.

The proof only calls
`residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_edgeMatrix`
and feeds the resulting residual positivity and residual negative-power
integrability pair into
`exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top`.

It does not construct a chart, prove a pushforward identity, transport density
or Jacobian factors, compare original `lossDLN`, produce normal crossings,
compute pole order, or extract an RLCT.

## Verification

Reviewer verification: focused Lean check of
`DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean` from the `lean/`
project root succeeded.
