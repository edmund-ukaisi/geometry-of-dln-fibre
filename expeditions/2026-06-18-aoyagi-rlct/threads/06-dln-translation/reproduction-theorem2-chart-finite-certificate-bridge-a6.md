# Reproduction - Theorem 2 chart finite-certificate bridge

Status: reproduced; Lean pending.

Source: Aoyagi 2023 PDF pp. 5-9, using the A0 normal-crossing discussion on
pp. 5-6 and the Theorem 2 displayed formulas on pp. 8-9.

## Purpose

The chart-certificate final boundary currently has a finite exponent formula
field:

```text
AoyagiTheorem2FiniteExponentFormulaHypothesis Cnc.exponentData L ell H r m data.
```

This slice replaces that opaque field by the finite witnesses already isolated
in A0:

- an active coordinate whose ratio is the displayed Theorem 2 `lambda`;
- a lower-bound proof against every active coordinate;
- a chart whose global-minimum count is the displayed order formula;
- a chart-count upper bound for every chart.

It is a finite bridge from source-facing chart certificates to the existing
Theorem 2 final socket.

## Pen-And-Paper Calculation

Let `Cnc` be a supplied normal-crossing chart certificate and let
`D = Cnc.exponentData`.  Assume a selected-width provenance equality

```text
m = aoyagiSelectedReducedWidths H r cuts.
```

Assume also the chart-level extraction hypothesis

```text
Cnc.ExtractionHypothesis lambda poleOrder,
```

which is only the cited analytic normal-crossing-to-RLCT boundary projected to
`D`.

For the finite formula field, A0 already proves:

```text
if p in D.activePairs
and D.ratioAt p = aoyagiTheorem2Lambda_fromCeilData L ell H r m data
and forall p' in D.activePairs,
      aoyagiTheorem2Lambda_fromCeilData L ell H r m data <= D.ratioAt p'
and D.minCountInChart c = data.theorem2OrderFormula
and forall c', D.minCountInChart c' <= data.theorem2OrderFormula,
then
  D.exponentMinimum = aoyagiTheorem2Lambda_fromCeilData L ell H r m data
  and D.exponentOrder = data.theorem2OrderFormula.
```

Those equalities are exactly the fields of
`AoyagiTheorem2FiniteExponentFormulaHypothesis D L ell H r m data`.  Together
with selected-width provenance and the chart-level extraction hypothesis, they
construct `AoyagiTheorem2SuppliedChartFinalBoundary`.

The already proved projection then gives:

```text
lambda = aoyagiTheorem2Lambda_fromCeilData L ell H r m data
poleOrder = data.theorem2OrderFormula.
```

## Boundary

This bridge does not construct `Cnc`, prove chart coverage, prove unit
nonvanishing analytically, prove the active-ratio lower bound, prove chart
count witnesses or upper bounds, prove Lemma 5, prove pole order without A0,
or extract RLCT.  It only reduces the final chart socket to explicit finite
witness obligations.

## Kill Conditions

- The constructor accepts a chart count at a non-global ratio.
- The active-pair lower bound ranges over only one chart rather than all active
  pairs.
- The chart-count upper bound ranges over only charts attaining the candidate
  ratio rather than all charts.
- The theorem is named as proving Theorem 2 rather than as a supplied
  chart-boundary constructor.
