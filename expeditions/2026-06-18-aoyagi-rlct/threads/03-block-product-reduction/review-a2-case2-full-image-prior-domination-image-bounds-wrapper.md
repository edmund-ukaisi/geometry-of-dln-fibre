# Review - A2 Case 2 full image prior domination from image bounds

Date: 2026-07-01.

Status: xhigh read-only review PASS.

## Checks

- The theorem is a wrapper of the existing full-image prior-domination theorem.
- The source-density hypothesis is correctly strengthened from
  `baseJ.restrict V`-a.e. lower bound to a pointwise lower bound on
  `sourceChart '' V`.
- The prior-density hypothesis is correctly strengthened from
  `originalVolume.restrict (sourceChart '' V)`-a.e. upper bound to a pointwise
  upper bound on `sourceChart '' V`.
- `sourceDensity z` is definitionally
  `sourceImageDensity (sourceChart z)`.
- The returned `MeasurableSet (sourceChart '' V)` supports the restricted
  measure argument for the prior-density upper bound.
- The pointwise bounds are correctly placed inside the existential package,
  after `V` has been returned.

## Boundary

The theorem is only a sufficient-condition wrapper.  It does not prove
positivity, boundedness, identification of `sourceImageDensity`, boundedness
of the prior density, determinant transport, raw Haar transport, image
coverage, normal crossings, pole order, or RLCT extraction.  No converse from
a.e. bounds to pointwise image bounds is claimed.

## Verification

Reviewer `Franklin` performed the read-only reproduction/theorem-shape check.
The controller then verified the implementation with focused elaboration,
focused module build, full local `lake build DLNFibre`, `scripts/sorries`,
`git diff --check`, and direct axiom probes.
