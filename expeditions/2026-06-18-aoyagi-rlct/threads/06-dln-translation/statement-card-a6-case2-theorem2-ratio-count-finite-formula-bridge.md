# Statement card - A6 Case 2 ratio-count finite formula bridge

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/Case2Theorem2FiniteExponentBridge.lean`

Name:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedContinuingA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_centerCard_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le`

## Claim

A supplied continuing Case 2/A0 exponent-coordinate bridge can populate the
Theorem 2 finite exponent formula boundary from chart counts stated at the
Case 2 candidate ratio, once that ratio has been proved to be the global
finite exponent minimum.

## Inputs Kept Explicit

- a supplied `D : AoyagiNormalCrossingExponentData`;
- a supplied coordinate `p : Fin D.numCharts × Fin D.numCoords`;
- a supplied chart `c : Fin D.numCharts`;
- a displayed continuing Case 2 certificate and bridge `B`;
- a supplied active-ratio lower bound at
  `card(case2ResidualBlockPivotEntries n S J)/2`;
- a supplied equality from that Case 2 ratio to
  `aoyagiTheorem2Lambda_fromCeilData Lthm ell H r m data`;
- a supplied chart-count equality at the Case 2 ratio;
- a supplied all-chart upper bound at the Case 2 ratio.

## Proved

```text
AoyagiTheorem2FiniteExponentFormulaHypothesis D Lthm ell H r m data
```

## Not Proved

No construction of `D`, `p`, or `c`; no proof of the active-ratio lower bound;
no proof of the Case 2/Theorem 2 lambda equality; no proof of the chart-count
facts; no selected-width provenance; no chart production; no analytic
normal-crossing certificate; no pole order; and no RLCT extraction.

## Verification

Focused and full gates passed:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Case2Theorem2FiniteExponentBridge.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.Case2Theorem2FiniteExponentBridge
cd lean && lake env lean DLNFibre.lean
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reported `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build reported only pre-existing Core linter warnings.

## Review

Xhigh source/math reviewer `Feynman the 2nd` passed the slice with boundary
warnings: chart-count facts remain substantial supplied obligations.  Xhigh
Lean/API reviewer `James the 2nd` passed the placement and proof shape and
requested the `_eq_of_forall_le` name suffix, which has been applied.

Durable review artifact:
`review-case2-theorem2-ratio-count-finite-formula-bridge-a6.md`.
