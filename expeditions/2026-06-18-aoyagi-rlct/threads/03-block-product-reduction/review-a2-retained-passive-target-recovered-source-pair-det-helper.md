# Review - A2 target-recovered source pair and determinant helper

Date: 2026-06-27.

Reviewer: xhigh `Epicurus the 2nd`.

Verdict: PASS.

## Findings

No formalisation or mathematical inaccuracies were found in the reviewed diff.

The determinant helper
`linearEquiv_prodCongr_det_eq_mul` is a thin wrapper over
`LinearEquiv.coe_prodCongr` and the existing
`linearMap_det_prodMap_eq_mul`, and belongs in the low-level determinant API.

The target-recovered source pair
`retainedPassiveTargetRecoveredSourcePairAt` is exactly the target-side
edge-pair shear followed by the point-specialized formal inverse.  The theorem
`retainedPassiveTargetRecoveredSourcePairAt_fderiv_eq_sourcePair` repackages
the existing recovery theorem without changing content.

The source-`C` projection
`retainedPassiveTargetRecoveredSourceCAt` and
`retainedPassiveTargetRecoveredSourceCAt_fderiv_eq_sourceC` correctly project
the second component of the recovered source pair.

## Boundary

These lemmas are useful recovery inputs for the target-normalizer frontier, but
they do not construct a determinant-one target normalizer or package the
recoveries as determinant-one linear equivalences.  The surrounding statement
cards and ledgers keep that boundary explicit.

