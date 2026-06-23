# Reproduction - Theorem 2 chart ratio-count bridge

Status: reproduced, formalised, and xhigh-reviewed.

Source: Aoyagi 2023 PDF pp. 5-9, using the A0 normal-crossing min/order
formula and the Theorem 2 displayed lambda/order formulas.

## Purpose

The chart finite-certificate bridge accepts chart counts already stated as
`minCountInChart`, meaning counts of coordinates whose ratio is the global
minimum.  Source-facing chart calculations often first count coordinates at a
displayed candidate ratio:

```text
countInChartAtRatio displayedLambda c.
```

This slice adds the finite bridge that consumes those ratio-specific counts
and rewrites them to global-minimum counts only after the active-coordinate
minimum proof identifies the displayed ratio with `exponentMinimum`.

## Pen-And-Paper Calculation

Let

```text
D = Cnc.exponentData
q = aoyagiTheorem2Lambda_fromCeilData L ell H r m data.
```

Assume:

```text
p in D.activePairs,
D.ratioAt p = q,
forall p' in D.activePairs, q <= D.ratioAt p'.
```

By the A0 finite minimum certificate,

```text
D.exponentMinimum = q.
```

Now assume ratio-specific chart-count data:

```text
D.countInChartAtRatio q c = data.theorem2OrderFormula,
forall c', D.countInChartAtRatio q c' <= data.theorem2OrderFormula.
```

Since `D.exponentMinimum = q`, A0 rewrites

```text
D.minCountInChart c' = D.countInChartAtRatio q c'
```

for every chart `c'`.  Therefore the supplied ratio-count witness and
all-chart upper bound prove

```text
D.exponentOrder = data.theorem2OrderFormula.
```

These two finite equalities fill
`AoyagiTheorem2FiniteExponentFormulaHypothesis D L ell H r m data`, and hence
the chart final boundary follows from selected-width provenance plus the
chart-level A0 extraction hypothesis.

## Boundary

This does not prove any active-ratio lower bound or any chart ratio-count
fact from source.  It does not construct the chart certificate, chart
coverage, analytic unit nonvanishing, Lemma 5 exactness, pole order without
A0, or RLCT extraction.

## Kill Conditions

- The ratio-specific count is used without first proving
  `D.exponentMinimum = q`.
- The all-chart upper bound is only checked for one chart.
- The theorem is advertised as proving the Theorem 2 order formula from
  Aoyagi's source, rather than reducing it to explicit finite ratio-count
  obligations.
