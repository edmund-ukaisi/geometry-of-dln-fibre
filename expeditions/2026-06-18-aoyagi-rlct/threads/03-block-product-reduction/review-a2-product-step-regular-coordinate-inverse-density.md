# Review - A2 p.13 regular-coordinate inverse density handoff

Date: 2026-06-26.

Verdict: accepted at the stated scope after naming/docstring fixes.

## Checks

- The raw-shaped target tuple order is correct:
  `(Ctop,D,F3,A1,F2,A3,C)`.
- The p. 13 left-endpoint tuple correctly uses
  `(Ctop(u),Dtail(x),F3(u),Ctop(u),F2(u),0,C0(x))`.
- The passive `A1` slot is `Ctop(u)`, not the identity.  The identity is the
  pre-left-step raw `C1` accumulator.
- The residual slots are split consistently: `Dtail` is the right tail
  residual product and `C0` is the left endpoint residual block.
- Determinant-chart membership only asks for the two `Ctop(u)` determinants.
- The continuity theorem uses the self-base hypothesis exactly where needed,
  to obtain the recursive determinant-chart hypotheses for suffix residual
  continuity.
- The positivity theorem is centered-coordinate only and does not require the
  self-base edge-family hypothesis; the Lean name was corrected to end in
  `_center`.

## Review Fixes

- Renamed
  `paperEndpointFixedBaseP13RawOrderTuple_inverseJacobianDensity_pos_selfBase`
  to
  `paperEndpointFixedBaseP13RawOrderTuple_inverseJacobianDensity_pos_center`.
- Changed the aggregate import comment from "unit bounds" to "handoff",
  because this module proves composed continuity and positivity, not composed
  lower/upper eventual bounds.
- Changed the determinant-membership docstring from "centered self-base" to
  "centered regular-coordinate".

## Boundary

This is a local tuple and reciprocal-density handoff.  It does not prove
source coverage, original DLN source/prior transport, unweighted measure
transport, normal crossings, pole order, or RLCT.
