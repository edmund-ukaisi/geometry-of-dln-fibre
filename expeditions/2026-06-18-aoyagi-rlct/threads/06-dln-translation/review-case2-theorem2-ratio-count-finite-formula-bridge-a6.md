# Review - Case 2 ratio-count finite formula bridge

Date: 2026-06-23.

Status: xhigh source/math and Lean/API reviews passed.

## Reviewed Artifact

- `lean/DLNFibre/DLN/Aoyagi/Case2Theorem2FiniteExponentBridge.lean`
- `reproduction-case2-theorem2-ratio-count-finite-formula-bridge-a6.md`
- `statement-card-a6-case2-theorem2-ratio-count-finite-formula-bridge.md`

Lean name reviewed:

```text
Case2DisplayedContinuingA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_centerCard_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le
```

## Source/Math Review

Reviewer: `Feynman the 2nd`.

Verdict: pass, with boundary warnings.

The reviewer confirmed that this bounded slice is mathematically sound if it
is advertised as a finite certificate replacement rather than a source proof
of the order formula.  Aoyagi pp. 5-6 support the finite normal-crossing
pattern: the exponent is the minimum active ratio and the order is the maximum
chartwise count of coordinates attaining that ratio.  Theorem 2 pp. 8-9
supports the displayed lambda and order formula targets.

The main warning is that the chart-count equality and all-chart upper bound
are substantial supplied obligations over the supplied exponent data `D`.
They are not proved by this slice.

## Lean/API Review

Reviewer: `James the 2nd`.

Verdict: pass, with a naming fix.

The reviewer confirmed that the theorem belongs in the existing
`Case2Theorem2FiniteExponentBridge.lean` leaf module and should keep `Lcase`
and `Lthm` separate.  The reviewer requested the name suffix
`_of_countInChartAtRatio_eq_of_forall_le` to match existing A0 and final
assembly API patterns.  The theorem was renamed accordingly.

The proof route is finite API composition:

```text
B.exponentMinimum_eq_centerCard_div_two_of_forall_le hleRatio
D.exponentOrder_eq_of_countInChartAtRatio_eq_of_forall_le hmin hchart hleChart
theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_centerCard_eq_fromCeilData
```

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

## Boundary

This review does not certify construction of `D`, the coordinate `p`, the
chart `c`, active-ratio lower bounds, chart-count facts, the Case 2/Theorem 2
lambda equality, selected-width provenance, chart production, analytic
normal-crossing extraction, pole order, or RLCT.
