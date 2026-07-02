# Review - A2 density pullback continuity to eventual bounds

Date: 2026-07-02.

Status: xhigh read-only review PASS.

## Checks

- The lower-bound helper uses the open neighborhood `Ioi epsilon` of
  `f x0`; this requires the strict hypothesis `epsilon < f x0`.
- The upper-bound helper uses the open neighborhood `Iio K` of `f x0`; this
  requires the strict hypothesis `f x0 < K`.
- The paired helper only packages the two generic results for
  `sourceImageDensity ∘ sourceChart` and `density ∘ sourceChart`.
- The result is not a full source-prior theorem and does not claim any
  density identification.

## Boundary

The helper batch is pure topology.  It does not prove positivity,
boundedness, source-image density identification, prior-density transport,
determinant Haar transport, raw-Haar normalization, source-image/rank
coverage, normal crossings, pole order, or RLCT extraction.

## Verification

Reviewer `Bacon` performed the read-only API and theorem-shape check.  The
controller verified direct elaboration, focused module build, and direct axiom
probes.  The three declarations report only
`[propext, Classical.choice, Quot.sound]`.
