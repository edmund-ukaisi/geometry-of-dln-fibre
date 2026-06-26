# Review - A2 p.13 left-step section-image measure

Date: 2026-06-26.

Reviewer: xhigh read-only landed-slice scout `Tesla the 2nd`.

Verdict: no blocking findings.

## Scope Checked

The reviewer checked the new theorem:

```text
map_p13RawOrderTuple_eq_map_leftStepRawOrder_image_of_measurable_edgeMatrix
```

in `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepRegularDensity.lean`.

## Findings

No blocking findings.

The theorem is scoped as a section-image identity.  Its conclusion is only

```text
Measure.map Y eta = Measure.map Phi (Measure.map X eta)
```

and the statement contains no raw Haar measure `m`, no `[m.IsAddHaarMeasure]`,
and no `withDensity` conclusion.

The p.13 guardrail is preserved.  The raw preimage tuple fixes `C1 = 1` and
`A3 = 0`, and the constructed left-step raw tuple is proved equal to that
preimage before this theorem uses it.  The existing explicit projection
guardrails for the actual tuple remain in place.

The Lean proof handles the API risks in the expected order: derive
`AEMeasurable raw eta`, push a.e. raw-chart membership through `Measure.map`,
import a.e. measurability of `Phi` from the restricted determinant chart, then
use `AEMeasurable.map_map_of_aemeasurable`.  Raw determinant-chart support is
used only to recover the `Ctop` unit condition needed for the pointwise p.13
algebra, not to assert full support or Haar transport.

## Verification

The reviewer did not run Lean and made no file edits.  Controller focused
verification is recorded in the statement card.
