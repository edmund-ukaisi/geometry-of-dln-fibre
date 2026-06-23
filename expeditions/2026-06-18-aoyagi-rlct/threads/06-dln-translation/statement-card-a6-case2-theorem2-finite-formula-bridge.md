# Statement card - A6 Case 2 to Theorem 2 finite formula bridge

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/Case2Theorem2FiniteExponentBridge.lean`

Name:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedContinuingA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_centerCard_eq_fromCeilData`

## Claim

A supplied continuing Case 2/A0 exponent-coordinate bridge can populate the
Theorem 2 finite exponent formula boundary once the remaining finite
identifications are supplied explicitly: the active-ratio lower bound, the
equality from the Case 2 center cardinality to Theorem 2's displayed lambda
formula, and the order equality.

## Inputs Kept Explicit

- a supplied `D : AoyagiNormalCrossingExponentData`;
- a supplied coordinate `p : Fin D.numCharts × Fin D.numCoords`;
- a displayed continuing Case 2 certificate and bridge `B`;
- a supplied lower bound over all active ratios;
- a supplied equality
  `card(case2ResidualBlockPivotEntries n S J)/2 =
   aoyagiTheorem2Lambda_fromCeilData Lthm ell H r m data`;
- a supplied equality `D.exponentOrder = data.theorem2OrderFormula`.

## Proved

```text
AoyagiTheorem2FiniteExponentFormulaHypothesis D Lthm ell H r m data
```

## Not Proved

No construction of `D` or `p`, no proof of the lower bound, no proof of the
Case 2 center-cardinality/Theorem 2 lambda equality, no proof of the order
formula, no selected-width provenance, no chart production, no analytic
normal-crossing certificate, no pole order, and no RLCT extraction.

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

Xhigh source/math reviewer `Raman the 2nd` passed the slice with no required
fixes.  Xhigh Lean/API reviewer `Dirac the 2nd` passed the module placement,
import shape, theorem statement, and proof shape with no required fixes.

Durable review artifact:
`review-case2-theorem2-finite-formula-bridge-a6.md`.
