# Statement card - A4 Case 2 continuing center-square/formal-Jacobian certificate

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `case2DisplayedPaperQ_isUnit`
- `case2DisplayedPaperQ_det_isUnit`
- `case2DisplayedPaperQinv_isUnit`
- `case2DisplayedPaperQinv_det_isUnit`
- `Case2DisplayedContinuingReindexedSourceChartCenterSqFormalJacobianCertificate`
- `sourceChartMap_continuingReindexedSourceChartCenterSqFormalJacobianCertificate`
- `Case2DisplayedContinuingReindexedSourceChartCertificate.exists_reindexedNextSourceProduct_with_PQ_det_units`

## Claim

Over an ordered field, the displayed continuing Case 2 local certificate can
be refined by carrying:

- the selected-entry center-square factorization;
- positivity, nonzero, and `IsUnit` witnesses for the normalized
  center-square factor through the existing unit certificate;
- the formal pivot-first determinant equality;
- the finite exponent identity saying the non-pivot determinant exponent is
  the residual-block center cardinality minus one;
- the finite relation saying the corrected new numerator is the formal
  determinant exponent plus one;
- determinant-unit witnesses for the displayed `Q/Q^-1` operations and the
  continuing certificate's supplied `P` row-operation witness.

## Inputs Kept Explicit

- `1 <= S`, `S <= L`;
- `J+1 <= prefixMinNat n (S+1)`;
- `J+2 <= prefixMinNat n (S+1)` for the continuing next-center guard;
- ordered field hypotheses for the coefficient type;
- the same pre-state exponent/level/gap hypotheses, supplied chart-family
  boundary, residual coordinates, and following factor as the existing
  continuing reindexed source-chart constructor.

## Proved

The new certificate contains the previous ordered-field unit certificate and:

```text
selectedEntryCenterSq (case2ResidualBlockPivotEntries n S J)
  (case2DisplayedSourceChartMap n hS hcont u residual)
 =
u^2 *
  selectedEntryCenterSqUnitFactor
    ((case2ResidualBlockPivotEntries n S J).erase (J+1,J+1)) residual
```

and

```text
det (selectedEntryPivotFirstJacobian u residual)
 =
u ^
  ((case2ResidualBlockPivotEntries n S J).erase (J+1,J+1)).card
```

together with

```text
((case2ResidualBlockPivotEntries n S J).erase (J+1,J+1)).card
 =
(case2ResidualBlockPivotEntries n S J).card - 1.
```

It also records

```text
((case2ResidualBlockPivotEntries n S J).erase (J+1,J+1)).card + 1
 =
(case2ResidualBlockPivotEntries n S J).card
```

and

```text
new corrected numerator
 =
(((case2ResidualBlockPivotEntries n S J).erase (J+1,J+1)).card + 1 : Nat)
```

as an integer equality.  Separately, the displayed `Q` and `Q^-1` finite
matrices are units with unit determinants, and the continuing certificate
exports a supplied `P` row-operation witness whose determinant is a unit.

## Not Proved

No analytic chart neighbourhood, no chart coverage, no transition regularity,
no analytic unit control for the later `P` and `Q` changes, no literal source
production of the p. 21 displayed equality with its apparent extra outside
`u`, no total DLN loss monomial identity, no differentiable Jacobian theorem,
no volume-form theorem, no A0 normal-crossing chart certificate, no pole
order, and no RLCT extraction.

## Verification

Controller ran:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
```

The focused check passed.

## Review

Xhigh source/math reviewer `Wegener the 2nd` passed the slice and confirmed
source fidelity to Aoyagi pp. 5-6 and pp. 19-22, including the p. 21 caveat
about the apparent extra outside `u`.  Xhigh Lean/API reviewer
`Mendel the 2nd` passed the Lean statement shape and finite-algebra boundary.

Durable review artifact:
`review-case2-continuing-center-sq-formal-jacobian-certificate-a4.md`.
