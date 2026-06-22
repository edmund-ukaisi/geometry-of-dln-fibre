# Reproduction - A6 supplied final assembly boundary

Date: 2026-06-22.

Status: final-socket composition boundary; formalisation-ready.

## Source Anchor

Aoyagi Theorem 2 is on PDF pp. 8-9.  The normal-crossing extraction interface
is the A0 cited boundary from PDF pp. 5-6.  The proof-side arithmetic feeding
this socket is the Lemma 5/Definition 3 material on PDF pp. 24-27; PDF p. 28
is conclusion/asymptotic discussion rather than a separate formal assembly
step.

This slice does not reproduce a new source calculation.  It packages the
already reproduced A6 formula translation and the already formalized A0/A6
finite-exponent bridge with explicit source-facing provenance hypotheses.

## Supplied Data

Let:

```text
D        = finite normal-crossing exponent data,
lambda   = external lambda value supplied through the A0 extraction interface,
poleOrder = external pole-order value supplied through the A0 extraction interface,
C        = selected cutpoints S_j,
m_j      = selected reduced widths,
data     = Definition 3 ceiling datum for m.
```

The final boundary keeps these hypotheses supplied:

```text
m = aoyagiSelectedReducedWidths H r C,
AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder,
AoyagiTheorem2FiniteExponentFormulaHypothesis D L ell H r m data.
```

The first field records source-facing selected-width provenance:
`m_j` is the integer reduced width `H(S_j)-r`.  The selected rank-width bounds
and strict source selected-width inequality are not fields of the final socket;
they remain explicit hypotheses on the auxiliary width lemmas.

The last two fields are the actual final socket:

```text
lambda = D.exponentMinimum,
poleOrder = D.exponentOrder,
D.exponentMinimum = displayed lambda formula,
D.exponentOrder = data.theorem2OrderFormula.
```

## Calculation

The formula projections are just transitivity:

```text
lambda
  = D.exponentMinimum
  = aoyagiTheorem2Lambda_fromCeilData L ell H r m data.
```

The already-proved formula rewrites give:

```text
lambda = aoyagiTheorem2Lambda_average L ell H r data.aParam m,
lambda = aoyagiTheorem2Lambda_expanded L ell H r data.aParam data.ceilWidth m.
```

For the order parameter:

```text
poleOrder
  = D.exponentOrder
  = data.theorem2OrderFormula
  = data.aParam * (ell - data.aParam) + 1.
```

The selected-width provenance fields also give finite bookkeeping:

```text
m_j = aoyagiReducedWidthInt H r (C.cut j).
```

Under a separately supplied selected rank-width hypothesis
`forall j, r <= H(C.cut j)`, Lean also gets the Nat-subtraction form and
nonnegativity.  Under a separately supplied strict selected-width inequality,
Lean gets `m_i <= data.ceilWidth - 1`.

## Lean Targets

Add `lean/DLNFibre/DLN/Aoyagi/Theorem2FinalAssembly.lean` with:

```text
AoyagiTheorem2SuppliedFinalBoundary
AoyagiTheorem2SuppliedFinalBoundary.selectedWidths_apply_eq_reducedWidthInt
AoyagiTheorem2SuppliedFinalBoundary.selectedWidths_eq_natCast_sub
AoyagiTheorem2SuppliedFinalBoundary.selectedWidths_nonneg
AoyagiTheorem2SuppliedFinalBoundary.selectedWidthNat_nonneg
AoyagiTheorem2SuppliedFinalBoundary.selectedWidth_le_pred
AoyagiTheorem2SuppliedFinalBoundary.lambda_eq_theorem2Lambda_fromCeilData
AoyagiTheorem2SuppliedFinalBoundary.lambda_eq_theorem2Lambda_average
AoyagiTheorem2SuppliedFinalBoundary.lambda_eq_theorem2Lambda_expanded
AoyagiTheorem2SuppliedFinalBoundary.poleOrder_eq_theorem2OrderFormula
AoyagiTheorem2SuppliedFinalBoundary.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula
AoyagiTheorem2SuppliedFinalBoundary.lambda_and_poleOrder_eq_expanded_and_orderFormula
AoyagiTheorem2SuppliedFinalBoundary.lambda_eq_theorem2Lambda_average_selectedReducedWidths
AoyagiTheorem2SuppliedFinalBoundary.lambda_eq_theorem2Lambda_expanded_selectedReducedWidths
```

## Nonclaims

This does not prove selected cutpoint existence, Definition 3 selection
inequalities, rank-width inequalities from a concrete product, source
parameter provenance, normal-crossing chart production, finite exponent
formula equalities, chart coverage, unit factors, Jacobian/prior exponent
correctness, Lemma 5 no-extra coverage, the Lemma 5 order count, pole order
without A0, or the analytic normal-crossing extraction theorem.
