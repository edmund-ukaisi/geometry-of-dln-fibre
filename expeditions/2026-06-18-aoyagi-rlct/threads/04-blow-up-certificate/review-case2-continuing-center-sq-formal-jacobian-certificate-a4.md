# Review - A4 Case 2 continuing center-square/formal-Jacobian certificate

Date: 2026-06-23.

Status: xhigh source/math and Lean/API reviews passed.

## Reviewed Artifact

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `reproduction-case2-continuing-center-sq-formal-jacobian-certificate-a4.md`
- `statement-card-a4-case2-continuing-center-sq-formal-jacobian-certificate.md`

Lean names reviewed:

```text
case2DisplayedPaperQ_isUnit
case2DisplayedPaperQ_det_isUnit
case2DisplayedPaperQinv_isUnit
case2DisplayedPaperQinv_det_isUnit
Case2DisplayedContinuingReindexedSourceChartCenterSqFormalJacobianCertificate
sourceChartMap_continuingReindexedSourceChartCenterSqFormalJacobianCertificate
Case2DisplayedContinuingReindexedSourceChartCertificate.exists_reindexedNextSourceProduct_with_PQ_det_units
```

## Source/Math Review

Reviewer: `Wegener the 2nd`.

Verdict: pass; no required fixes.

The reviewer checked Aoyagi PDF pp. 5-6 and pp. 19-22.  The source supports:

- the sum-of-squares ideal convention and finite `(h+1)/(2k)` bookkeeping;
- the displayed Case 2 selected-entry chart
  `d_{J+1,J+1}=u` and all other residual-block entries equal to
  `u` times a primed coordinate;
- the corrected residual-block count
  `(M(S)-J)(M^(S+1)-J)`;
- unitriangular `Q/P` operations as finite determinant-unit operations.

The pen-and-paper arithmetic was confirmed:

```text
sum x_e^2 = u^2 * (1 + sum y_e^2),
det [1 0; y uI] = u^|E'|,
|E'| + 1 = |E|.
```

Thus the corrected new numerator is the formal pivot-first determinant
exponent plus one.  The reviewer also confirmed that the docs correctly avoid
formalising the suspect literal p. 21 equality with an apparent extra outside
`u` after p. 20 defines `b'_i = u b_i`.

## Lean/API Review

Reviewer: `Mendel the 2nd`.

Verdict: pass; no required fixes.

The reviewer confirmed:

- `Q/Qinv` names are locally scoped and follow existing
  `case2DisplayedPaper*` naming;
- determinant-unit statements remain finite algebra over `[CommRing R]`;
- the ordered-field content remains isolated in the center-square/unit
  certificate;
- the new certificate coherently refines
  `Case2DisplayedContinuingReindexedSourceChartUnitCertificate`;
- proofs delegate to existing helper lemmas rather than rebuilding the
  arithmetic inline;
- the docs preserve the finite-algebra boundary.

## Verification

Focused checks passed:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic
```

The first Lake build produced a style warning about a two-goal tactic in the
new constructor; the controller fixed it and reran the focused Lean check
successfully.

## Boundary

This review does not certify chart coverage, transition regularity, analytic
unit neighbourhoods, analytic control of all `P/Q` changes, a differentiable
Jacobian or volume-form theorem, a total loss monomial identity, an
`AoyagiNormalCrossingChartCertificate`, pole order, or RLCT extraction.
