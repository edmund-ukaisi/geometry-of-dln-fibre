# Statement Card - A6 Case 2 regular-shift finite formula bridge

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/Case2Theorem2FiniteExponentBridge.lean`

Names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedContinuingA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_regularVariableCountShift_of_forall_le_of_centerCard_add_regularTerm_eq_fromCeilData`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedContinuingA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_regularVariableCountShift_of_forall_le_of_centerCard_add_regularTerm_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le`

## Claim

A supplied continuing Case 2/A0 exponent-coordinate bridge can populate the
finite Theorem 2 formula boundary for the regular-variable shifted exponent
datum, provided the reduced Case 2 center ratio plus Aoyagi's regular term is
identified with the displayed Theorem 2 lambda formula and the reduced finite
order formula is supplied or derived from chart counts.

## Inputs Kept Explicit

- reduced exponent datum `D`;
- displayed continuing Case 2 certificate and bridge `B`;
- endpoint rank bounds `r <= H 1` and `r <= H (Lthm+1)`;
- active-ratio lower bound for the reduced Case 2 center ratio;
- shifted lambda equality
  `card(case2ResidualBlockPivotEntries n S J)/2 + regularTerm =
   aoyagiTheorem2Lambda_fromCeilData Lthm ell H r m data`;
- reduced order equality `D.exponentOrder = data.theorem2OrderFormula`, or
  reduced chart-count hypotheses at the Case 2 center ratio.

## Proved

```text
AoyagiTheorem2FiniteExponentFormulaHypothesis
  (D.jacobianPriorLossShift
    (aoyagiTheorem2RegularVariableCount Lthm H r))
  Lthm ell H r m data
```

## Not Proved

No construction of `D`, no construction of the coordinate bridge, no active
lower-bound theorem, no proof of the shifted lambda equality, no proof of the
order formula, no regular-suspension chart, no analytic ideal transport, no
normal-crossing production, no pole order, and no RLCT extraction.

## Verification

Focused module build passed:

```text
cd lean && env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.Case2Theorem2FiniteExponentBridge
```

Review:
`review-case2-theorem2-regular-shift-finite-formula-bridge-a6.md`.
