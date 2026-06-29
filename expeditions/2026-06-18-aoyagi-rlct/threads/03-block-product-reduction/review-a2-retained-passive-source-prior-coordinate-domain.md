# Review - A2 Retained-Passive Source-Prior Coordinate Domain

Reviewer: Noether the 3rd, xhigh read-only review.

## Verdict

PASS.

No blocking source-fidelity, math, or formalisation-boundary issue was found.

## Checks

- Aoyagi Lemma 2 signs are represented correctly:
  `F2 = -A1^{-1} A2`, `F3 = -A3 A1^{-1}`, and
  `C4 = -A3 A1^{-1} A2 + A4`.
- The Theorem 3 induction formulas use the right signs:
  `C^(S+1) = -A3' (A1')^{-1} A2' + A4'`,
  `F2'' = -(A1')^{-1} A2'`, and
  `F3'' = F3' - D A3' (C1' A1')^{-1}`.
- The p.13 product-difference lower-right block is recorded as
  `prod C^(s) - F3 F2`, not as the uncorrected residual product.
- The retained-passive coordinate-domain fields match the Lean structure
  dimensions for `RetainedPassiveNonredundantCoordinateData`.
- The note correctly separates three statements: full retained-passive
  determinant-chart COV, passive selected-entry chart-produced measure, and
  an external/original source-prior comparison.
- The next-target constraints do not treat the reduced selected-entry section
  as full Haar measure or as an original source prior.

## Wording Repair

The note was patched after review to:

- rename `Lean-Ready Consequence` to `Next Lean Target Constraints`;
- describe the inverse result as a coordinate inverse on the
  determinant/source-recursive charts;
- name `sourceReadback_edgeMatrix_eq` and
  `edgeMatrix_sourceReadback_eq_of_sourceRecursiveDetChart`.

## Nonclaims

No new Lean theorem, source-prior transport, selected-entry image coverage,
determinant-chart Haar theorem, source-rank coverage, normal crossings, pole
order, or RLCT result is claimed by this review.
