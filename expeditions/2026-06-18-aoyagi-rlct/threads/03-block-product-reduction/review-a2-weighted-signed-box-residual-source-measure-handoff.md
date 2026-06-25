# Review - A2 weighted signed-box residual source-measure handoff

Date: 2026-06-25.

Reviewer: xhigh subagent Arendt the 5th.

Scope:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/reproduction-a2-weighted-signed-box-residual-source-measure-handoff.md
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/statement-card-a2-weighted-signed-box-residual-source-measure-handoff.md
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/thread.md
expeditions/2026-06-18-aoyagi-rlct/priorities.md
```

## Findings

No blocking findings.  No major mathematical or scoping issue found.

The theorem is sound as a weighted signed-box source-measure constructor.  It
assumes the weighted pushforward and chart-side bounds, then derives only the
residual positivity/integrability pair on `μ.restrict source`; it does not
construct the chart, density, Jacobian, original-loss comparison, normal
crossings, pole order, or RLCT.

The hypotheses are sufficient and honest: a.e.-measurability of
`ofReal density`, chart a.e.-measurability on the signed box, exact weighted
pushforward, positive residual-set measurability, constants and critical
inequalities, and the residual/density a.e. bounds.

The `withDensity` lower-integral rewrite is sound.  The proof uses
`lintegral_withDensity_eq_lintegral_mul_non_measurable₀` with the assumed
a.e.-measurability and automatic finiteness of `ENNReal.ofReal density`, then
identifies the product with `ofReal ((residual ^ (-t)) * density)` a.e. using
`density >= 0`.

## Low Documentation Finding

The original reproduction calculation block did not restate the Lean-only
measurability premises.  This was not an overclaim because the statement card
listed them explicitly.  The controller amended the reproduction note to state
that the Lean theorem assumes a.e.-measurability of `ofReal density`, chart
a.e.-measurability, and measurability of the source positive residual set.

## Residual Risks

- No chart construction.
- No proof of the weighted pushforward identity.
- No Jacobian/density construction or regularity.
- No original DLN loss comparison.
- No endpoint or divergent-side theorem.
- No normal-crossing production, pole order, or RLCT extraction.

## Verdict

Approved as mathematically and formalisation-scope sound.

The reviewer performed a read-only source review and did not edit files.  The
controller ran the Lean build gates separately.
