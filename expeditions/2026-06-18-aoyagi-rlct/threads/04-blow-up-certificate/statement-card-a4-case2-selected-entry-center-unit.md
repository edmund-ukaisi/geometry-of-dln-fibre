# Statement card - A4 Case 2 selected-entry center unit factor

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `selectedEntryCenterSq_nonneg`
- `selectedEntryCenterSqUnitFactor`
- `selectedEntryCenterSqUnitFactor_pos`
- `selectedEntryCenterSqUnitFactor_ne_zero`
- `selectedEntryCenterSqUnitFactor_isUnit`
- `case2DisplayedSourceChartMap_centerSqUnitFactor_pos`
- `case2DisplayedSourceChartMap_centerSqUnitFactor_ne_zero`
- `case2DisplayedSourceChartMap_centerSqUnitFactor_isUnit`

## Claim

The normalized selected-entry square-sum factor

```text
1 + selectedEntryCenterSq center residual
```

is positive under Lean's ordered commutative semiring hypotheses.  Hence it is
nonzero, and over an ordered field it is a unit.

The displayed Case 2 wrapper applies this to the erased residual-block center
appearing in the displayed selected-entry chart.

## Inputs Kept Explicit

- finite center and residual coordinates;
- ordered commutative semiring hypotheses, expressed in Lean's unbundled order
  hierarchy, for the generic positivity/nonzero lemmas;
- ordered field, expressed as `[Field K] [LinearOrder K]
  [IsStrictOrderedRing K]`, for `IsUnit`;
- displayed Case 2 source context `1 <= S` and
  `J+1 <= prefixMinNat n (S+1)` in the source-facing wrappers.

## Proved

```text
0 <= selectedEntryCenterSq center residual
0 < 1 + selectedEntryCenterSq center residual
(1 + selectedEntryCenterSq center residual) != 0
IsUnit (1 + selectedEntryCenterSq center residual)
```

with displayed Case 2 specializations for

```text
(case2ResidualBlockPivotEntries n S J).erase (J+1,J+1).
```

## Not Proved

No analytic chart neighbourhood, no chart coverage, no transition regularity,
no differentiable Jacobian theorem, no unit control for the later `P` and `Q`
regular changes, no A0 normal-crossing chart certificate, no pole order, and
no RLCT extraction.

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

Xhigh source/math reviewer `Pascal the 2nd` passed the slice and confirmed
source fidelity to Aoyagi p. 5 and pp. 19-21, with the ordered-field boundary
kept explicit.  Xhigh Lean/API reviewer `Hegel the 2nd` passed the slice and
confirmed that the fresh ordered-field `{K}` unit statements avoid the
ambient semiring/ring typeclass diamond.

Durable review artifact:
`review-case2-selected-entry-center-unit-a4.md`.
