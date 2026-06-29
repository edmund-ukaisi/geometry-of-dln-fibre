# Review - A2 source-stratum bounds local-source finite integral

Date: 2026-06-29.

Reviewer: xhigh subagent `Parfit the 2nd`.

## Verdict

PASS. No findings.

## Scope

Read-only review of the Lean theorem

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_bounds_locally_subset_localSource
```

in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean`.

## Review Notes

The theorem API stays within the intended bridge scope.  Its assumptions are
source-stratum loss/density bounds, explicit local coverage
`Ulocal ∩ sourceStratum ⊆ Ulocal ∩ localSource`, and residual
positivity/integrability on `localSource`; the conclusion is only finite
integrability over `U ∩ sourceStratum`.

No hidden chart or RLCT overreach was found.  The proof only shrinks `Ubounds`
by `Ulocal`, derives `U ∩ sourceStratum ⊆ localSource` from the explicit
coverage hypothesis, and invokes the finite-side p.13 adapter.  The
`sourceData` package remains documented as excluding chart coverage, Jacobian
compatibility, normal crossings, and RLCT.

The measure and a.e. directions are correct.  The proof establishes that the
smaller product measure is bounded by the larger one, transfers larger-measure
a.e. bounds to the smaller measure with `ae_mono`, and uses the same monotone
restriction pattern through `residualSourceHypotheses_mono` for residual
positivity and integrability.

The reviewer did not run Lean or a build; the controller's focused build and
standard checks are recorded in the statement card.
