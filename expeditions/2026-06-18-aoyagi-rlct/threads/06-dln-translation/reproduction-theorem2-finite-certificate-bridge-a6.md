# Reproduction - Theorem 2 finite certificate bridge

Date: 2026-06-22.

Status: A0/A6 finite-socket bridge over supplied min/order certificates.

## Source Boundary

Aoyagi PDF pp. 5-6 gives the finite normal-crossing formula after a
normal-crossing chart has been supplied: the exponent is the minimum active
ratio, and the order is the maximum chartwise number of coordinates attaining
that global minimum.  Aoyagi Theorem 2's displayed formula is on PDF pp. 8-9.

The analytic extraction theorem remains the only cited boundary.  This slice
does not construct charts or prove the inequalities that identify the
candidate minimum and order.

## Data

Let:

```text
D    : AoyagiNormalCrossingExponentData,
data : AoyagiDefinition3CeilData ell m,
q    = aoyagiTheorem2Lambda_fromCeilData L ell H r m data,
N    = data.theorem2OrderFormula.
```

The finite exponent boundary needs:

```text
D.exponentMinimum = q,
D.exponentOrder   = N.
```

## Minimum Certificate

Suppose a supplied active coordinate `p` satisfies:

```text
p in D.activePairs,
D.ratioAt p = q,
forall p' in D.activePairs, q <= D.ratioAt p'.
```

By the A0 finite minimum certificate,

```text
D.exponentMinimum = q.
```

## Order Certificate

Suppose a supplied chart `c` satisfies:

```text
D.minCountInChart c = N,
forall c', D.minCountInChart c' <= N.
```

By the A0 finite order certificate,

```text
D.exponentOrder = N.
```

## Result

The two certified equalities fill the two fields of
`AoyagiTheorem2FiniteExponentFormulaHypothesis`.

If the A0 extraction hypothesis is also supplied, the existing bridge gives:

```text
lambda = q,
poleOrder = N.
```

## Lean Names

```text
AoyagiTheorem2FiniteExponentFormulaHypothesis.of_activePair_ratioAt_eq_of_forall_le_of_chart_minCount_eq_of_forall_le
AoyagiTheorem2FiniteExponentFormulaHypothesis.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_activePair_chartCount
```

## Nonclaims

This does not construct normal-crossing exponent data, chart coverage, units,
Jacobian/prior exponents, active-ratio lower bounds, chart-count upper bounds,
Lemma 5 no-extra coverage, pole order without A0, or RLCT extraction.

## Kill Conditions

- The active coordinate witness for the minimum is required; lower bounds
  alone are insufficient.
- The order is a maximum over chartwise counts, not a sum over charts.
- The counted coordinates are those attaining the global minimum, not merely a
  chart-local minimum.
- The final `lambda`/`poleOrder` pair requires the explicit A0 extraction
  hypothesis.
