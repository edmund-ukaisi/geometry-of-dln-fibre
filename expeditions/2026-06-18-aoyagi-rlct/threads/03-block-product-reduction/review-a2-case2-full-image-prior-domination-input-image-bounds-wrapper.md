# Review - A2 Case 2 full image prior domination from input-image bounds

Date: 2026-07-01.

Status: xhigh read-only review PASS.

## Checks

- The theorem is a wrapper of the returned-image-bound full prior theorem.
- The replacement hypotheses on `sourceChart '' G` are strictly stronger than
  the existing hypotheses on `sourceChart '' V`, because the returned package
  includes `V subset G`.
- No injectivity, continuity, or measurability of `sourceChart '' G` is needed
  for the image-containment step.
- The determinant-side domination and finite scalar conclusion are unchanged.
- The input-image bounds remain inside the theorem's post-`V` implication
  package, so the statement does not pretend to prove the bounds before the
  local chart data is fixed.

## Boundary

The theorem is only a sufficient-condition wrapper.  It does not prove the
input-image bounds, does not prove `sourceChart '' G` is a measurable or open
source-side neighborhood, and does not close determinant Haar transport,
raw-Haar normalization, source-image/rank coverage, normal crossings, pole
order, or RLCT extraction.

## Verification

Reviewer `Lagrange` performed the read-only reproduction/theorem-shape check.
The controller then verified the implementation with focused elaboration,
focused module build, full local `lake build DLNFibre`, `scripts/sorries`,
`git diff --check`, and a direct axiom probe.
