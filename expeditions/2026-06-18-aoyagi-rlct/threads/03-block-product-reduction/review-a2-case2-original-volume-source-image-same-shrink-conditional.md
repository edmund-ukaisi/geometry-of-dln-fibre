# Review - A2 Case 2 original-volume source-image same-shrink conditional

Date: 2026-07-01.

Status: controller review PASS for the conditional boundary; verification
passed.

## Checks

- The theorem must keep the raw-Haar raw-source pushforward as an explicit
  hypothesis.
- The source-chart image package and the measure identity must use the same
  local `V`.
- The chart-piece hypothesis should be `chartPiece subset sourceChart '' V`;
  p.13 source-set containment should be derived from the local pointwise
  source theorem, not assumed separately.
- The density should be the constant inverse Haar scalar from the existing
  p.13 raw-order/original-volume bridge.
- The theorem should not be described as the missing original-volume transport
  theorem.

## Source Boundary Review

Xhigh source-boundary review found that Aoyagi p.13 supports the block
algebra and regular-variable count, but not an unconditional comparison
between original edge-family volume and the passive-theta source-image
measure.  Removing the raw-Haar raw-source pushforward hypothesis would
require a separate local change-of-variables/Jacobian theorem.

## Boundary

This is a conditional socket for downstream finite-integral consumers.  It
does not prove raw-Haar identification, determinant-chart Haar transport,
source-image coverage, source-rank coverage, original source-prior transport,
normal crossings, pole order, or RLCT extraction.

## Verification

Focused elaboration, focused module build, full local `lake build DLNFibre`,
`lean/scripts/sorries`, `git diff --check`, and direct axiom probe passed.
The direct axiom probe reported only
`[propext, Classical.choice, Quot.sound]`.
