# Reproduction - normal-crossing finite min/order certificates

Date: 2026-06-22.

Status: finite A0 bookkeeping over supplied normal-crossing exponent data.

## Source Boundary

Aoyagi PDF pp. 5-6 gives the normal-crossing finite extraction shape: take
the minimum of the active ratios

```text
(h_j+1)/(2 k_j),  k_j > 0,
```

and take the order/multiplicity from the number of coordinates attaining that
minimum, chart by chart, using the maximum chartwise count.

The analytic extraction theorem remains the A0 cited boundary.  This slice is
only finite min/max bookkeeping after the chart exponent data have already
been supplied.

## Minimum Certificate

Let `D.activeRatios` be the finite set of active ratios and

```text
D.exponentMinimum = min D.activeRatios.
```

To prove a candidate `q` is the exponent minimum it is enough to prove:

```text
q in D.activeRatios,
forall r in D.activeRatios, q <= r.
```

Then:

```text
D.exponentMinimum <= q
```

because the finite minimum is below every member, and

```text
q <= D.exponentMinimum
```

because `D.exponentMinimum` itself is a member of `D.activeRatios`.

Equivalently, it suffices to exhibit an active coordinate `p` with

```text
D.ratioAt p = q
```

and prove `q <= D.ratioAt p'` for every active coordinate `p'`.

## Order Certificate

Let `D.chartMinCounts` be the finite set of chartwise counts and

```text
D.exponentOrder = max D.chartMinCounts.
```

To prove a candidate `q` is the exponent order it is enough to prove:

```text
q in D.chartMinCounts,
forall r in D.chartMinCounts, r <= q.
```

Then:

```text
q <= D.exponentOrder
```

because the finite maximum is above every member, and

```text
D.exponentOrder <= q
```

because `D.exponentOrder` itself is a member of `D.chartMinCounts`.

Equivalently, it suffices to exhibit a chart `c` with

```text
D.minCountInChart c = q
```

and prove `D.minCountInChart c' <= q` for every chart `c'`.

## Lean Names

```text
AoyagiNormalCrossingExponentData.exponentMinimum_eq_of_mem_activeRatios_of_forall_le
AoyagiNormalCrossingExponentData.exponentMinimum_eq_of_activePair_ratioAt_eq_of_forall_le
AoyagiNormalCrossingExponentData.exponentOrder_eq_of_mem_chartMinCounts_of_forall_le
AoyagiNormalCrossingExponentData.exponentOrder_eq_of_chart_minCount_eq_of_forall_le
AoyagiNormalCrossingExponentData.exponentOrder_eq_of_forall_le_of_exists_chart_minCount_eq
```

## Nonclaims

This does not construct charts, prove normal crossings, prove the active-ratio
lower bounds from Aoyagi's blow-up recursion, identify chartwise counts with
Lemma 5 terminal labels, prove pole order without the A0 extraction
hypothesis, or extract an RLCT.

## Kill Conditions

- Do not treat a candidate ratio as active unless membership in
  `D.activeRatios` or an active coordinate witness is supplied.
- Do not treat a candidate order as a maximum unless a realizing chart count
  and all-chart upper bound are supplied.
- Do not use these finite certificates as a substitute for chart production or
  analytic extraction.
