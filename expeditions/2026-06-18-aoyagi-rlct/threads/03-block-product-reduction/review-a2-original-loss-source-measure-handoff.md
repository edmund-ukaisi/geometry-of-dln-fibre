# Review - A2 original loss source-measure handoff

Date: 2026-06-25.

Reviewer: Leibniz the 5th, xhigh, read-only.

Status: passed.

## Findings

No blockers were found.

The review covered the new self-base original-loss theorem in
`EndpointLossComparison.lean`, the new
`OriginalLossSourceMeasure.lean` module, the aggregator import, and the
associated original-loss notes.

The Lean statements keep the scope narrow.  The self-base theorem composes the
existing adapted p.13 lower bound with the endpoint basis comparison.  The
constant bookkeeping uses `c = a * b0`; multiplying the `(a / 2) * S` bound by
positive `b0` gives `b0 * ((a / 2) * S)`, which rewrites to
`((a * b0) / 2) * S`.

The source-measure wrappers are restricted to
`mu.restrict (U ∩ sourceStratum)`.  The product version asserts only a
first-coordinate property over `(mu.restrict (U ∩ sourceStratum)).prod nu`,
not a fiber-uniform product-coordinate bound.

Controller verification after review:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/OriginalLossSourceMeasure.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.OriginalLossSourceMeasure
cd lean && lake env lean DLNFibre.lean
lean/scripts/sorries
git diff --check
```

All passed.  `lean/scripts/lb` was attempted but environment escalation was
rejected, so the shared-build wrapper result is not available for this slice.

## Boundary

This review certifies only the source-filter-to-restricted-source-a.e. handoff
for concrete square-Frobenius `lossDLN` on `chainMapMatrixTuple b (Cedge x)`.
It does not certify product chart construction, an independent regular fiber
variable, signed-box pushforward, density/Jacobian transport, normal crossings,
pole order, or RLCT extraction.
