# Review - Case 1 to Theorem 2 finite formula bridge

Date: 2026-06-23.

Status: xhigh source/math and Lean/API review passed.

## Reviewed Artifact

- `lean/DLNFibre/DLN/Aoyagi/Case1Theorem2FiniteExponentBridge.lean`
- `reproduction-case1-theorem2-finite-formula-bridge-a6.md`
- `statement-card-a6-case1-theorem2-finite-formula-bridge.md`

Lean names reviewed:

```text
Case1SelectedEntryA0ExponentCoordinateBridge.theorem2CandidateRatio
Case1SelectedEntryA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData
Case1SelectedEntryA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le
Case1SelectedOldUnitA0ExponentCoordinateBridge.theorem2CandidateRatio
Case1SelectedOldUnitA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData
Case1SelectedOldUnitA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le
```

## Review

Reviewer: xhigh independent reviewer `Huygens`.

Verdict: pass; no findings.

The reviewer confirmed that the finite bridge keeps the intended supplied
obligations explicit: the Case 1/A0 coordinate bridge, the candidate-ratio
identification with `aoyagiTheorem2Lambda_fromCeilData`, the active-ratio
lower bound, and either a supplied order equality or chart-count witnesses.
No overclaiming, quiver-paper leakage, source-boundary loss, or API/name
mismatch was found.

The direct PDF extraction tools were unavailable in the reviewer environment,
so the source-fidelity check used the existing Aoyagi-local reproduction trail
and the Lean boundary shape.

## Verification

The reviewer ran:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Case1Theorem2FiniteExponentBridge
```

The command passed.

Controller final gates also passed:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Case1Theorem2FiniteExponentBridge DLNFibre.DLN.Aoyagi.Case1Theorem2ChartFinalBridge
cd lean && scripts/lb
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reported `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build reported only pre-existing Core linter warnings.

## Boundary

This review does not certify construction of the exponent data `D`, the
coordinate `p`, active-ratio lower bounds, the candidate-ratio/Theorem 2 lambda
equality, order equality, chart-count facts, selected-width provenance, chart
production, analytic extraction, pole order, or RLCT.
