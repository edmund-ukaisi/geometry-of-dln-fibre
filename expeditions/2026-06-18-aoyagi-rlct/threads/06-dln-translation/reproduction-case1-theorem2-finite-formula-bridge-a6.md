# Reproduction - Case 1 to Theorem 2 finite formula bridge

Date: 2026-06-23.

Status: reproduced, formalised, and reviewed.

Review: `review-case1-theorem2-finite-formula-bridge-a6.md`.

## Source Boundary

Aoyagi PDF pp. 5-6 computes the finite normal-crossing exponent from active
ratios

```text
(h_j + 1) / (2 k_j).
```

Theorem 2's displayed lambda and order formulas are the source-facing finite
arithmetic on PDF pp. 8-9.  The selected-old Case 1 local calculation on PDF
pp. 15-16 supplies, after the previous A4/A0 bridge, a candidate active
coordinate with ratio

```text
(1 + J1 * (n (S + 1) - J)) / 2.
```

This slice only composes those finite interfaces under explicit supplied
equalities and bounds.

## Pen-and-Paper Calculation

Let

```text
q_case1 = (1 + J1 * (n (S + 1) - J)) / 2,
q_T2    = aoyagiTheorem2Lambda_fromCeilData L ell H r m data,
N_T2    = data.theorem2OrderFormula.
```

The previous Case 1/A0 bridge proves, from a supplied coordinate bridge `B`
and an explicit lower bound over all active ratios,

```text
D.exponentMinimum = q_case1.
```

If the Theorem 2 lambda identification is also supplied,

```text
q_case1 = q_T2,
```

then

```text
D.exponentMinimum = q_T2.
```

If the order equality is supplied independently,

```text
D.exponentOrder = N_T2,
```

then the two fields of
`AoyagiTheorem2FiniteExponentFormulaHypothesis D L ell H r m data` are filled.

There is also a count-at-candidate variant.  Once the active-ratio lower bound
has proved `D.exponentMinimum = q_case1`, supplied chart counts at `q_case1`

```text
D.countInChartAtRatio q_case1 c = N_T2,
forall c', D.countInChartAtRatio q_case1 c' <= N_T2
```

prove the finite order equality `D.exponentOrder = N_T2`.

## Lean Target

Add a leaf module importing the Case 1 finite bridge and the generic Theorem
2 finite bridge:

```text
lean/DLNFibre/DLN/Aoyagi/Case1Theorem2FiniteExponentBridge.lean
```

with:

```text
Case1SelectedEntryA0ExponentCoordinateBridge.theorem2CandidateRatio
Case1SelectedEntryA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData
Case1SelectedEntryA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le
Case1SelectedOldUnitA0ExponentCoordinateBridge.theorem2CandidateRatio
Case1SelectedOldUnitA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData
Case1SelectedOldUnitA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le
```

## Boundary

This slice does not prove:

- construction of `D` or the coordinate `p`;
- the active-ratio lower bound;
- the equality from the Case 1 candidate ratio to Theorem 2's lambda formula;
- the order equality or the chart-count facts;
- selected-width provenance;
- chart production, chart coverage, or analytic unit nonvanishing;
- analytic Jacobian/volume-form control;
- the normal-crossing extraction theorem, pole order, or RLCT.

## Kill Conditions

- Keep the Case 1 blow-up parameters separate from Theorem 2's formula
  parameters.
- Do not derive the order field from the minimum bridge unless chart-count
  facts at the Case 1 candidate ratio are explicitly supplied.
- Do not use this theorem as a final Theorem 2 statement without selected
  width provenance and the explicit A0 extraction hypothesis.
