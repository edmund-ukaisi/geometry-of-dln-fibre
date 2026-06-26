# Reproduction - Case 2 regular-shift finite formula bridge

Date: 2026-06-26.

Status: reproduced, formalised, and reviewed.

Statement card:
`statement-card-a6-case2-theorem2-regular-shift-finite-formula-bridge.md`.
Review:
`review-case2-theorem2-regular-shift-finite-formula-bridge-a6.md`.

## Source Boundary

Aoyagi Theorem 2, PDF pp. 8-9, states the displayed final lambda formula and
order formula.  The p. 13 product-reduction display separates a regular
block-entry contribution from the reduced finite singular product.  The Case 2
continuing local calculation on PDF pp. 19-22 supplies a reduced finite
candidate ratio after the A4/A0 bridge:

```text
q_case = card(case2ResidualBlockPivotEntries n S J) / 2.
```

The source does not state that `q_case` alone equals the full Theorem 2 lambda.
The source-faithful comparison is:

```text
q_case + aoyagiTheorem2RegularTerm L H r
  = aoyagiTheorem2Lambda_fromCeilData L ell H r m data.
```

This slice formalises exactly that shifted finite-exponent handoff.

## Pen-and-Paper Calculation

Let `D` be the reduced finite normal-crossing exponent datum and let

```text
Dshift =
  D.jacobianPriorLossShift
    (aoyagiTheorem2RegularVariableCount L H r).
```

The Case 2/A0 exponent-coordinate bridge proves, under a supplied lower bound
over all active reduced ratios,

```text
D.exponentMinimum = q_case.
```

The regular-variable finite shift proves, under endpoint rank bounds
`r <= H 1` and `r <= H (L+1)`,

```text
Dshift.exponentMinimum =
  D.exponentMinimum + aoyagiTheorem2RegularTerm L H r
```

and preserves finite order:

```text
Dshift.exponentOrder = D.exponentOrder.
```

Therefore, if the shifted lambda identification and reduced order equality are
supplied,

```text
q_case + aoyagiTheorem2RegularTerm L H r
  = aoyagiTheorem2Lambda_fromCeilData L ell H r m data,

D.exponentOrder = data.theorem2OrderFormula,
```

then

```text
AoyagiTheorem2FiniteExponentFormulaHypothesis
  Dshift L ell H r m data
```

follows by transitivity.  The chart-count variant first derives the reduced
order equality from chart counts at the reduced Case 2 ratio, then applies the
same shift.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/Case2Theorem2FiniteExponentBridge.lean
```

New theorems:

```text
Case2DisplayedContinuingA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_regularVariableCountShift_of_forall_le_of_centerCard_add_regularTerm_eq_fromCeilData

Case2DisplayedContinuingA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_regularVariableCountShift_of_forall_le_of_centerCard_add_regularTerm_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le
```

The proof composes:

- `B.exponentMinimum_eq_centerCard_div_two_of_forall_le`;
- `AoyagiTheorem2FiniteExponentFormulaHypothesis.of_regularVariableCountShift`;
- in the chart-count variant,
  `D.exponentOrder_eq_of_countInChartAtRatio_eq_of_forall_le`.

## Boundary

This slice does not prove:

- construction of the reduced exponent datum `D`;
- construction of the coordinate bridge `B`;
- the active-ratio lower bound;
- the shifted equality from the reduced Case 2 center ratio plus regular term
  to Theorem 2's displayed lambda;
- the reduced order equality or chart-count hypotheses;
- regular-suspension chart construction or analytic ideal transport;
- normal-crossing production, pole order, or RLCT extraction.

## Kill Conditions

- Do not replace the shifted equality by the older raw equality
  `q_case = aoyagiTheorem2Lambda_fromCeilData ...` when working toward the
  full Theorem 2 formula.
- Do not treat `D.jacobianPriorLossShift ...` as a constructed analytic
  regular-suspension chart; it is finite exponent-array arithmetic.
- Keep endpoint rank bounds or the rank-width source of those endpoint bounds
  explicit.
