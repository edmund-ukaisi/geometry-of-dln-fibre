# Reproduction - Theorem 2 ratio-count terminal-order bridge

Date: 2026-06-22.

Status: A0/A5/A6 finite ratio-count handoff.

## Source Boundary

Aoyagi PDF pp. 5-6 gives the finite normal-crossing formula after charts are
supplied.  Theorem 2's displayed lambda formula is on PDF pp. 8-9, and Lemma
5's terminal count discussion is on PDF pp. 25-27.

This slice is a finite handoff only.  It lets later source-facing certificates
state chart counts against the displayed Theorem 2 lambda value, then rewrites
those counts to the internal `D.exponentMinimum` counts using the active-ratio
minimum certificate.

## Data

Let:

```text
D    : AoyagiNormalCrossingExponentData,
data : AoyagiDefinition3CeilData (n+1) m,
TC   : AoyagiLemma5SuppliedTerminalCandidateFamily
         ... n data.aParam data.ceilWidth m ...
q    = aoyagiTheorem2Lambda_fromCeilData L (n+1) H r m data.
```

## Minimum Certificate

Assume:

```text
p in D.activePairs,
D.ratioAt p = q,
forall p' in D.activePairs, q <= D.ratioAt p'.
```

Then the A0 finite active-ratio certificate gives:

```text
D.exponentMinimum = q.
```

## Ratio-Count Certificate

Assume a chart `c` satisfies:

```text
D.countInChartAtRatio q c = TC.terminalMinimumLabels.card,
forall c', D.countInChartAtRatio q c' <= TC.terminalMinimumLabels.card.
```

Using `D.exponentMinimum = q`, A0 rewrites `countInChartAtRatio q c'` to
`minCountInChart c'` for every chart.  The finite maximum certificate then
gives:

```text
D.exponentOrder = TC.terminalMinimumLabels.card.
```

## Terminal-Order Rewrite

With supplied branch-label injectivity and the supplied terminal upper bound,

```text
Set.InjOn TC.branchLabel TC.fullBranches,
TC.terminalMinimumLabels.card <= data.theorem2OrderFormula,
```

the A5 terminal-order bridge gives:

```text
TC.terminalMinimumLabels.card = data.theorem2OrderFormula.
```

Therefore both fields of the A6 finite exponent formula boundary are filled:

```text
D.exponentMinimum = q,
D.exponentOrder = data.theorem2OrderFormula.
```

## Final Assembly

With selected-width provenance and A0 extraction also supplied,

```text
m = aoyagiSelectedReducedWidths H r C,
AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder,
```

the supplied final boundary gives:

```text
lambda = aoyagiTheorem2Lambda_fromCeilData L (n+1) H r m data,
poleOrder = data.theorem2OrderFormula.
```

## Lean Names

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_activePair_ratioCount_terminalMinimumLabels_card
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_activePair_ratioCount_terminalMinimumLabels_card
AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_activePair_ratioCount_terminalMinimumLabels_card
```

## Nonclaims

This does not construct normal-crossing charts, prove active-ratio lower
bounds, prove chart counts at the displayed lambda, prove chart-count upper
bounds, prove source-backed chart-count/terminal-label identification, prove
branch-label injectivity, prove the terminal upper bound, prove Lemma 5
no-extra coverage, prove pole order without A0, prove normal crossings, or
prove RLCT extraction.

## Kill Conditions

- Counts at the displayed lambda become global-minimum counts only because the
  active-ratio certificate proves `D.exponentMinimum = q`.
- `countInChartAtRatio` still filters by positive loss exponent.
- The terminal-label equality still depends on supplied branch-label
  injectivity and the supplied terminal upper bound.
