# Review - Lemma 5 counted-datum classifier order-formula bridge

Date: 2026-06-22.

Reviewers: controller; xhigh independent checkers `Planck the 2nd` and
`Goodall the 2nd`; API scout `Parfit the 2nd`.

## Verdict

Accepted as a finite A5 handoff wrapper, with the same freeze boundary:
A5 remains supplied for source-backed terminal exactness.  This patch routes
an already supplied counted-datum classifier into the Theorem 2 order-formula
upper bound, and then reuses the existing branch-label-injectivity squeeze.

## Source/Fidelity Check

`Planck the 2nd` independently recommended freezing A5 as a supplied boundary.
The checker noted that Htilde interval counts and Definition 3 arithmetic are
already formalised, while the remaining source gaps are label-to-vector,
minimum-to-lambda, classifier, Case 1(2) uniqueness/injection, and
back-to-label maps.  The new theorems do not claim to fill those gaps.

`Goodall the 2nd` independently recommended exactly this finite handoff shape:
first route a supplied counted-datum classifier to the final order-formula
upper bound, then add supplied branch-label injectivity for equality.  `Parfit
the 2nd` mapped the surrounding A5 API and found no source-free constructor for
the missing classifier/back-to-label data in the current Lean surface.

## Kill Conditions Checked

- The counted-datum classifier is supplied.
- Branch-label injectivity remains supplied.
- The theorem proves only the cardinal upper bound/equality in
  `data.theorem2OrderFormula` notation.
- It does not call the cardinal equality pole order or RLCT.
- It does not use the printed Eq3/Eq4/Eq5 formulas as a source-backed
  classifier.

## Verification

Focused Lean check:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5TerminalOrderBridge.lean
```
