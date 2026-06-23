# Statement card - A4 Case 2 continuing reindexed source-chart unit certificate

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `Case2DisplayedContinuingReindexedSourceChartUnitCertificate`
- `sourceChartMap_continuingReindexedSourceChartUnitCertificate`

## Claim

Over an ordered field, the displayed continuing Case 2 local certificate can
be refined by carrying the selected-entry normalized center-square unit
factor

```text
selectedEntryCenterSqUnitFactor
  ((case2ResidualBlockPivotEntries n S J).erase (J+1,J+1)) residual
```

together with positivity, nonzero, and `IsUnit` witnesses.

## Inputs Kept Explicit

- `1 <= S`, `S <= L`;
- `J+1 <= prefixMinNat n (S+1)`;
- `J+2 <= prefixMinNat n (S+1)` for the continuing next-center guard;
- ordered field hypotheses for the coefficient type;
- the same pre-state exponent/level/gap hypotheses, supplied chart-family
  boundary, residual coordinates, and following factor as the existing
  continuing reindexed source-chart constructor.

## Proved

The new certificate contains:

```text
toReindexedSourceChartCertificate :
  Case2DisplayedContinuingReindexedSourceChartCertificate ...
centerSqUnitFactor_pos :
  0 < selectedEntryCenterSqUnitFactor erasedCenter residual
centerSqUnitFactor_ne_zero :
  selectedEntryCenterSqUnitFactor erasedCenter residual != 0
centerSqUnitFactor_isUnit :
  IsUnit (selectedEntryCenterSqUnitFactor erasedCenter residual)
```

where

```text
erasedCenter =
  (case2ResidualBlockPivotEntries n S J).erase (J+1,J+1).
```

## Not Proved

No analytic chart neighbourhood, no chart coverage, no transition regularity,
no unit control for Aoyagi's later `P` and `Q` changes, no total loss unit, no
differentiable Jacobian theorem, no A0 normal-crossing chart certificate, no
pole order, and no RLCT extraction.

## Verification

Controller ran:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic
cd lean && lake env lean DLNFibre.lean
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reports `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build succeeds with only pre-existing Core warnings.

## Review

Xhigh source/math reviewer `Lorentz the 2nd` passed the slice with the strict
A4-local ordered-field boundary.  Xhigh Lean/API reviewer `Godel the 2nd`
passed the statement shape and independently reran the focused Lean check.

Durable review artifact:
`review-case2-continuing-reindexed-source-chart-unit-certificate-a4.md`.
