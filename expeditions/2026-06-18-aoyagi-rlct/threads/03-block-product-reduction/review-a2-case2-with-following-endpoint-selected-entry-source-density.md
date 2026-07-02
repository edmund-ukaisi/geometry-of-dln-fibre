# Review - A2 with-following endpoint selected-entry source density

Date: 2026-07-02.

Reviewer: Descartes the 2nd, xhigh read-only sidecar audit.

Verdict: PASS.

## Findings

No blocking issue was found.

The four Lean declarations match the statement card.  The unweighted source is
the product of passive-field reference measure, unsigned selected-entry center
box, and following-factor reference measure.  The existing reference source
uses the same passive and following factors but replaces the center box by the
selected-entry weighted center box.

Density orientation is correct.  The density

```text
case2PassiveThetaWithFollowingFactorSelectedEntrySourceDensity
```

depends only on `z.1.yNext`, so it is pulled back from the passive-theta center
coordinate and does not charge the independent following matrix.

The selected-entry density is counted exactly once.  The proof first rewrites
`passiveRef.prod weightedBox` with `prod_withDensity_right₀`, then carries the
same density through the following-factor product with `prod_withDensity_left₀`.
The final density is `centerDensity z.1.yNext`, not a product of two density
factors.

The endpoint theorem only substitutes the source-measure equality into the
named endpoint image definition

```text
Measure.map Y (referenceSource.restrict Ω).
```

It does not assert determinant-chart Haar, raw Haar, source coverage, normal
crossings, pole order, or RLCT.

## Verification

The reviewer replayed:

```text
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
```

from the `lean/` Lake root.
