# Reproduction - Theorem 2 terminal-order bridge

Date: 2026-06-22.

Status: A5-to-A6 supplied-order handoff.

## Source Boundary

Aoyagi Theorem 2 is on PDF pp. 8-9.  The finite order expression is the
displayed multiplicity/order factor

```text
a(ell-a)+1.
```

Lemma 5's terminal arithmetic is on PDF pp. 25-27.  The preceding A5 audit
keeps the no-extra terminal-minimum coverage, branch-label injectivity, and
terminal upper bound as supplied boundaries.  This slice does not reopen that
source frontier.

The A0 normal-crossing extraction hypothesis remains the only analytic
citation boundary.

## Data

Let:

```text
D    : AoyagiNormalCrossingExponentData,
data : AoyagiDefinition3CeilData (n+1) m,
TC   : AoyagiLemma5SuppliedTerminalCandidateFamily
         ... n data.aParam data.ceilWidth m ...
```

The A6 finite exponent socket needs:

```text
D.exponentMinimum = aoyagiTheorem2Lambda_fromCeilData L (n+1) H r m data,
D.exponentOrder   = data.theorem2OrderFormula.
```

The first equality is not affected by this slice and remains supplied.  For
the second equality, we now allow the order count to pass through Lemma 5:

```text
D.exponentOrder = TC.terminalMinimumLabels.card.
```

Together with supplied branch-label injectivity and the supplied terminal
upper bound

```text
TC.terminalMinimumLabels.card <= data.theorem2OrderFormula,
```

the previous terminal-order bridge proves

```text
TC.terminalMinimumLabels.card = data.theorem2OrderFormula.
```

Therefore

```text
D.exponentOrder
  = TC.terminalMinimumLabels.card
  = data.theorem2OrderFormula.
```

This constructs the finite exponent formula boundary from the supplied
minimum equality and this decomposed order route.

## Final Assembly

If the selected-width provenance and A0 extraction hypothesis are also
supplied,

```text
m = aoyagiSelectedReducedWidths H r C,
AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder,
```

then the existing final assembly socket gives:

```text
lambda = aoyagiTheorem2Lambda_fromCeilData L (n+1) H r m data,
poleOrder = data.theorem2OrderFormula.
```

## Lean Names

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_terminalMinimumLabels_card
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_terminalMinimumLabels_card
AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_terminalMinimumLabels_card
```

## Nonclaims

This does not prove the exponent minimum formula, construct normal-crossing
charts, identify the chart-order count with terminal-minimum labels, prove
Lemma 5 no-extra coverage, prove branch-label injectivity from source, prove
the terminal upper bound from source, prove pole order without A0, or prove
RLCT extraction.

## Kill Conditions

- Do not read `D.exponentOrder = TC.terminalMinimumLabels.card` as proved by
  Lemma 5; it is a supplied chart/order identification.
- Do not infer branch-label injectivity or the terminal upper bound from the
  printed Eq3/Eq4/Eq5 families.
- Do not present the final pair theorem as an unconditional Theorem 2.
