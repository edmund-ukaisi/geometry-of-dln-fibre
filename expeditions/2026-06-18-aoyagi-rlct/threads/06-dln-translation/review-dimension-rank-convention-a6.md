# Review - A6 Dimension/Rank Convention

Date: 2026-06-22.

Reviewer posture: xhigh source/API checks plus controller review.

Verdict: pass as a small convention-map slice.

## Scope Review

The slice adds no analytic content.  It records the explicit local hypothesis

```text
r <= H s
```

and proves elementary consequences for the integer reduced width
`(H s : Int) - r`.

## Boundary Review

The theorem names do not claim that rank-width inequalities follow from a
matrix product, from Theorem 3, or from the normal-crossing certificate.  The
hypotheses remain explicit and pointwise.  The selected-width wrappers are
pointwise consequences only; they do not prove the selected cutpoint
inequalities from Aoyagi Definition 3.

The xhigh source check confirmed the source requirements: Aoyagi's source
layers are one-based, Definition 3 uses `M^(s)=H^(s)-r`, and the Nat bridge is
faithful only under `r <= H^(s)`.  It also flagged the PDF p. 8 input/output
orientation wording hazard; this slice follows the displayed matrix/product
orientation only.

The xhigh Lean/API check recommended local `rank_le` hypotheses and the
Nat-indexed `aoyagiSelectedWidthNat` accessor wrappers used downstream.  The
implemented API follows that shape and does not introduce a global
`forall s : Nat` rank-width definition.

This slice does not prove product reduction, chart coverage, pole order,
normal crossings, or RLCT extraction.

## Verification

Controller verification passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/FinalFormula.lean
lake build DLNFibre.DLN.Aoyagi.FinalFormula
lake build DLNFibre
scripts/sorries
git diff --check
```
