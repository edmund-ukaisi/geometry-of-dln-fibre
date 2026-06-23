# Reproduction - Case 2 to Theorem 2 finite formula bridge

Date: 2026-06-23.

Status: reproduced, formalised, and reviewed.

Review:
`review-case2-theorem2-finite-formula-bridge-a6.md`.

## Source Boundary

Aoyagi PDF pp. 5-6 computes the exponent from the finite normal-crossing
ratios

```text
(h_j + 1) / (2 k_j)
```

over active coordinates.  Theorem 2's displayed lambda and order formulas are
the source-facing finite arithmetic on PDF pp. 8-9.  The continuing Case 2
local calculation on PDF pp. 19-22 supplies, after the earlier A4 bridge, a
candidate active coordinate with ratio

```text
card(case2ResidualBlockPivotEntries n S J) / 2.
```

This slice only composes those finite interfaces under explicit supplied
equalities and bounds.

## Pen-and-Paper Calculation

Let

```text
q_case = card(case2ResidualBlockPivotEntries n S J) / 2,
q_T2   = aoyagiTheorem2Lambda_fromCeilData L ell H r m data,
N_T2   = data.theorem2OrderFormula.
```

The previous Case 2/A0 bridge proves, from a supplied coordinate bridge `B`
and an explicit lower bound over all active ratios,

```text
D.exponentMinimum = q_case.
```

If the Theorem 2 lambda identification is also supplied,

```text
q_case = q_T2,
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

## Lean Target

Add a leaf module importing both the Case 2 finite bridge and the generic
Theorem 2 finite bridge:

```text
lean/DLNFibre/DLN/Aoyagi/Case2Theorem2FiniteExponentBridge.lean
```

with theorem:

```text
Case2DisplayedContinuingA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_centerCard_eq_fromCeilData
```

The theorem consumes:

- a supplied Case 2/A0 coordinate bridge;
- an explicit lower bound
  `forall p' in D.activePairs, q_case <= D.ratioAt p'`;
- an explicit equality `q_case = q_T2`;
- an explicit equality `D.exponentOrder = N_T2`.

It proves:

```text
AoyagiTheorem2FiniteExponentFormulaHypothesis D L ell H r m data
```

## Boundary

This slice does not prove:

- construction of `D` or the coordinate `p`;
- the active-ratio lower bound;
- the equality from the Case 2 center cardinality to Theorem 2's lambda
  formula;
- the order equality;
- chart production, chart coverage, or analytic unit nonvanishing;
- analytic Jacobian/volume-form control;
- the normal-crossing extraction theorem, pole order, or RLCT.

## Kill Conditions

- Keep the Case 2 level parameter separate from Theorem 2's formula parameter;
  do not silently identify them.
- Do not derive the order field from the minimum bridge.
- Do not use this theorem as a final Theorem 2 statement without the explicit
  A0 extraction hypothesis and selected-width provenance.
