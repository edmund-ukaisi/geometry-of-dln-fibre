# Reproduction - Case 1 chart-final boundary bridge

Date: 2026-06-23.

Status: reproduced, formalised, and reviewed.

Review: `review-case1-theorem2-chart-final-bridge-a6.md`.

## Source Boundary

This is a small API handoff, not a source-moving result.  The previous Case 1
finite bridge builds

```text
AoyagiTheorem2FiniteExponentFormulaHypothesis Cnc.exponentData Lthm ell H r m data
```

from a supplied selected-old Case 1/A0 coordinate bridge, active-ratio lower
bound, Case 1/Theorem 2 lambda equality, and chart-count witnesses at the Case
1 candidate ratio.  The chart-final boundary also needs selected-width
provenance and the chart-level A0 extraction hypothesis.

## Pen-and-Paper Calculation

Assume:

```text
B : Case1SelectedOldUnitA0ExponentCoordinateBridge cert Cnc.exponentData p,
hselected : m = aoyagiSelectedReducedWidths H r cuts,
hNC : Cnc.ExtractionHypothesis lambda poleOrder,
```

plus the finite Case 1 ratio hypotheses:

```text
q_case1 = aoyagiTheorem2Lambda_fromCeilData Lthm ell H r m data,
forall p' in Cnc.exponentData.activePairs,
  q_case1 <= Cnc.exponentData.ratioAt p',
Cnc.exponentData.countInChartAtRatio q_case1 c = data.theorem2OrderFormula,
forall c',
  Cnc.exponentData.countInChartAtRatio q_case1 c'
    <= data.theorem2OrderFormula.
```

The finite Case 1 ratio-count bridge gives the finite exponent formula field.
Together with `hselected` and `hNC`, this fills the three fields of

```text
AoyagiTheorem2SuppliedChartFinalBoundary
  Cnc Lthm ell H r cuts m data lambda poleOrder.
```

## Lean Target

Add a leaf module:

```text
lean/DLNFibre/DLN/Aoyagi/Case1Theorem2ChartFinalBridge.lean
```

with theorem:

```text
Case1SelectedOldUnitA0ExponentCoordinateBridge.theorem2SuppliedChartFinalBoundary_of_forall_le_of_candidateRatio_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le
```

## Boundary

This slice does not construct `Cnc`, `cert`, `p`, or `c`; does not prove chart
coverage, normal crossings, unit nonvanishing, active-ratio lower bounds,
chart-count facts, the Case 1/Theorem 2 lambda equality, selected cutpoints,
selected-width provenance, analytic extraction, pole order, or RLCT.

## Kill Conditions

- Advertise this as a supplied chart-final boundary wrapper, not as Case 1
  Theorem 2 or an RLCT theorem.
- Keep `hNC` explicit; no analytic extraction theorem is proved.
- Keep chart counts at the Case 1 candidate ratio; do not silently replace
  them by counts at another displayed value.
