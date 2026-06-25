# Review - A2 source-rank stratum measurability

Date: 2026-06-25.

Reviewer: xhigh subagent Popper the 5th.

Scope:

```text
lean/DLNFibre/DLN/Aoyagi/ChartTopology.lean
lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/reproduction-a2-source-rank-stratum-measurability.md
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/statement-card-a2-source-rank-stratum-measurability.md
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/thread.md
expeditions/2026-06-18-aoyagi-rlct/priorities.md
```

## Findings

No blocking findings.

The determinantal rank bridge is mathematically sound: `rank <= r` is reduced
to vanishing of all `(r+1)` minors, with the reverse direction using
independent rows and then independent columns to produce a nonzero minor.

Exact rank is treated as measurable, not open: `rank <= r` is closed, and
`rank = r+1` is a measurable difference of two closed-rank loci.  The
reproduction, statement card, and thread notes correctly state the
non-openness nonclaim.

The source-stratum wrapper does not overclaim.  Measurability is proved under
continuous finite-basis coordinate matrices, or under globally continuous
`Cedge`; it does not derive measurability from `ContinuousAt Cedge x0`.

No Aoyagi-independence violation was found.  The reviewed Lean files import
only Aoyagi modules plus Mathlib at the surface, with no quiver-specific or
RLCT dependency in the inspected direct import chain.

## Verdict

Approved as mathematically and formalisation-scope sound.

The reviewer performed a read-only source review and did not edit files.  The
controller ran the Lean build gates separately.
