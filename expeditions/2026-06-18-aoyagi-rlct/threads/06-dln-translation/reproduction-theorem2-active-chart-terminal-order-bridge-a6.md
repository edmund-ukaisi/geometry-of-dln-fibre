# Reproduction - Theorem 2 active chart-terminal-order bridge

Date: 2026-06-22.

Status: A0/A5/A6 finite min/max certificate composition.

## Source Boundary

Aoyagi PDF pp. 5-6 gives the finite normal-crossing formula after
normal-crossing charts have been supplied.  The exponent is the finite minimum
of active ratios `(h+1)/(2k)`, and the order is the finite maximum, over
charts, of the number of active coordinates attaining the global minimum.
Aoyagi Theorem 2's displayed formula is on PDF pp. 8-9.  Lemma 5's terminal
count discussion is on PDF pp. 25-27.

This slice does not add a source theorem.  It composes the A0 finite minimum
and chart-count maximum certificate lemmas with the A5 terminal-order handoff
in Theorem 2 notation.  The analytic normal-crossing extraction theorem
remains the only cited boundary.

## Data

Let:

```text
D    : AoyagiNormalCrossingExponentData,
data : AoyagiDefinition3CeilData (n+1) m,
TC   : AoyagiLemma5SuppliedTerminalCandidateFamily
         ... n data.aParam data.ceilWidth m ...
q    = aoyagiTheorem2Lambda_fromCeilData L (n+1) H r m data.
```

The finite exponent formula boundary needs:

```text
D.exponentMinimum = q,
D.exponentOrder   = data.theorem2OrderFormula.
```

The preceding active-ratio terminal-order bridge still supplied:

```text
D.exponentOrder = TC.terminalMinimumLabels.card.
```

Here that equality is replaced by a finite chart-count maximum certificate.

## Minimum Reproduction

Assume a supplied active coordinate `p` satisfies:

```text
p in D.activePairs,
D.ratioAt p = q,
forall p' in D.activePairs, q <= D.ratioAt p'.
```

Since `D.exponentMinimum` is the finite minimum of active ratios, this gives:

```text
D.exponentMinimum = q.
```

## Chart-Count Reproduction

Assume a supplied chart `c` satisfies:

```text
D.minCountInChart c = TC.terminalMinimumLabels.card,
forall c', D.minCountInChart c' <= TC.terminalMinimumLabels.card.
```

Since `D.exponentOrder` is the finite maximum of the chartwise
global-minimum counts, this gives:

```text
D.exponentOrder = TC.terminalMinimumLabels.card.
```

This is still finite bookkeeping over supplied normal-crossing exponent data.
It does not say that `c` is produced by Aoyagi's chart construction or that
the chart count equals terminal labels by source geometry.

## Terminal-Order Rewrite

Assume the remaining supplied Lemma 5 obstruction in Theorem 2 notation:

```text
Set.InjOn TC.branchLabel TC.fullBranches,
TC.terminalMinimumLabels.card <= data.theorem2OrderFormula.
```

The A5 terminal-order bridge gives:

```text
TC.terminalMinimumLabels.card = data.theorem2OrderFormula.
```

Therefore:

```text
D.exponentOrder
  = TC.terminalMinimumLabels.card
  = data.theorem2OrderFormula.
```

## Final Assembly

With selected-width provenance and A0 extraction also supplied,

```text
m = aoyagiSelectedReducedWidths H r C,
AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder,
```

the existing supplied final boundary gives:

```text
lambda = aoyagiTheorem2Lambda_fromCeilData L (n+1) H r m data,
poleOrder = data.theorem2OrderFormula.
```

## Lean Names

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_activePair_chartCount_terminalMinimumLabels_card
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_activePair_chartCount_terminalMinimumLabels_card
AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_activePair_chartCount_terminalMinimumLabels_card
```

## Nonclaims

This does not construct normal-crossing charts, produce exponent data from the
blow-up recursion, prove active-ratio lower bounds, prove chart-count upper
bounds, identify chart counts with terminal-minimum labels from source,
prove branch-label injectivity, prove the terminal upper bound, prove Lemma 5
no-extra coverage, prove pole order without A0, prove normal crossings, or
prove RLCT extraction.

## Kill Conditions

- The chart-count witness is essential; upper bounds alone do not produce a
  finite maximum equality.
- The chart-count certificate counts coordinates attaining the global
  exponent minimum in one chart, not all terminal labels directly.
- The terminal-label equality still depends on supplied branch-label
  injectivity and the supplied terminal upper bound.
- The pair theorem is conditional on selected-width provenance and the A0
  extraction hypothesis; it is not an unconditional Theorem 2.
