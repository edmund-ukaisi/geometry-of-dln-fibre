# Reproduction - Theorem 2 active-ratio terminal-order bridge

Date: 2026-06-22.

Status: A0/A5/A6 finite-socket composition.

## Source Boundary

Aoyagi PDF pp. 5-6 gives the finite normal-crossing formula after a
normal-crossing chart system has been supplied: the exponent is the minimum
active ratio `(h+1)/(2k)`, and the order is the maximum number of
global-minimum coordinates in one chart.  Aoyagi Theorem 2's displayed
formula is on PDF pp. 8-9.  Lemma 5's terminal count discussion is on
PDF pp. 25-27.

This slice does not add a new source theorem.  It composes already isolated
finite interfaces: the A0 active-ratio finite-minimum certificate and the A5
terminal-order handoff in Aoyagi Theorem 2 notation.  The normal-crossing
extraction theorem remains the only cited analytic boundary.

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

The older terminal-order handoff still supplied the first equality directly.
Here the first equality is replaced by the A0 finite active-ratio
certificate.

## Minimum Reproduction

Assume a supplied active coordinate `p` satisfies:

```text
p in D.activePairs,
D.ratioAt p = q,
forall p' in D.activePairs, q <= D.ratioAt p'.
```

By the A0 definition, `D.exponentMinimum` is the finite minimum of
`D.ratioAt` over `D.activePairs`.  Since `p` is an active coordinate whose
ratio is exactly `q`, and `q` is a lower bound for every active ratio, the
finite minimum is `q`:

```text
D.exponentMinimum = q.
```

No chart production or source inequality is proved here.  The active witness
and the lower bound are supplied obligations.

## Order Reproduction

Assume the chart/order comparison is supplied:

```text
D.exponentOrder = TC.terminalMinimumLabels.card.
```

Assume also the remaining supplied Lemma 5 obstruction in Theorem 2 notation:

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
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_activePair_terminalMinimumLabels_card
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_activePair_terminalMinimumLabels_card
AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_activePair_terminalMinimumLabels_card
```

## Nonclaims

This does not construct normal-crossing charts, produce exponent data from the
blow-up recursion, prove active-ratio lower bounds from source charts,
identify chart-order counts with terminal-minimum labels, prove branch-label
injectivity, prove the terminal upper bound, prove Lemma 5 no-extra coverage,
prove pole order without A0, prove normal crossings, or prove RLCT
extraction.

## Kill Conditions

- The active coordinate witness is essential; lower bounds alone do not
  produce a finite minimum equality.
- The active-ratio certificate proves only `D.exponentMinimum = q`, not that
  the supplied `D` came from Aoyagi's charts.
- The order route still depends on the supplied chart/order equality and the
  supplied Lemma 5 obstruction.
- The pair theorem is conditional on selected-width provenance and the A0
  extraction hypothesis; it is not an unconditional Theorem 2.
