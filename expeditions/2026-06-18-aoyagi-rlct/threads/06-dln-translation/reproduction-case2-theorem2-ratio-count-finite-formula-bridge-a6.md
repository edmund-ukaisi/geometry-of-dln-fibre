# Reproduction - Case 2 ratio-count finite formula bridge

Date: 2026-06-23.

Status: reproduced, formalised, and reviewed.

Review:
`review-case2-theorem2-ratio-count-finite-formula-bridge-a6.md`.

## Source Boundary

Aoyagi PDF pp. 5-6 computes the exponent from the finite active ratios and
the order from the maximum number of coordinates attaining that global
minimum in a chart.  The continuing Case 2/A0 bridge supplies a candidate
ratio

```text
q_case = card(case2ResidualBlockPivotEntries n S J) / 2.
```

This slice only replaces a raw supplied order equality by source-facing
chart-count hypotheses at `q_case`.  It still does not prove those counts from
Aoyagi's chart construction.

## Pen-and-Paper Calculation

Assume the supplied Case 2/A0 coordinate bridge `B` and the active-ratio lower
bound

```text
forall p' in D.activePairs, q_case <= D.ratioAt p'.
```

The previous Case 2 minimum theorem gives:

```text
D.exponentMinimum = q_case.
```

If a chart `c` and all-chart bound are supplied at this same ratio,

```text
D.countInChartAtRatio q_case c = data.theorem2OrderFormula,
forall c', D.countInChartAtRatio q_case c' <= data.theorem2OrderFormula,
```

then, because `q_case` is the global exponent minimum, these are exactly
global-minimum coordinate counts.  The A0 finite order certificate therefore
gives:

```text
D.exponentOrder = data.theorem2OrderFormula.
```

Together with the supplied lambda identification

```text
q_case = aoyagiTheorem2Lambda_fromCeilData Lthm ell H r m data,
```

the exponent-minimum and exponent-order fields of
`AoyagiTheorem2FiniteExponentFormulaHypothesis` are filled.

## Lean Target

Add to `Case2Theorem2FiniteExponentBridge.lean`:

```text
Case2DisplayedContinuingA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_centerCard_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le
```

The theorem consumes:

- a supplied Case 2/A0 coordinate bridge;
- an explicit active-ratio lower bound at `q_case`;
- an explicit equality from `q_case` to Theorem 2's displayed lambda formula;
- a supplied chart whose `countInChartAtRatio q_case` is
  `data.theorem2OrderFormula`;
- a supplied all-chart upper bound for `countInChartAtRatio q_case`.

It proves:

```text
AoyagiTheorem2FiniteExponentFormulaHypothesis D Lthm ell H r m data
```

## Boundary

This slice does not prove:

- construction of `D`, the coordinate `p`, or the chart `c`;
- active-ratio lower bounds;
- the equality from `q_case` to Theorem 2's lambda formula;
- the chart-count equality or all-chart upper bound;
- selected-width provenance, chart production, analytic normal-crossing data,
  pole order, or RLCT extraction.

## Kill Conditions

- The chart counts must be at `q_case`, not at an unrelated displayed value.
- The chart counts become order counts only after `q_case` is proved to be
  `D.exponentMinimum`.
- The order is a maximum over chartwise counts, not a sum over charts.
