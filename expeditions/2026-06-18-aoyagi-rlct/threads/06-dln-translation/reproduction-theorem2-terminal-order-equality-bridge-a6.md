# Reproduction - Theorem 2 terminal order equality bridge

Date: 2026-06-23.

Status: finite A6 handoff.  This note does not repair the A5 source-backed
Lemma 5 exactness obstruction.

## Exact Terminal Count As Input

Suppose a supplied terminal-candidate family `TC` has already been counted in
final Theorem 2 notation:

```text
TC.terminalMinimumLabels.card = data.theorem2OrderFormula.
```

This input may come from the generic supplied Lemma 5 exactness route, from a
counted-datum classifier route, or from the Eq5 endpoint-family supplied
payload route.  The A6 bridge should not care how the equality was produced.

## Finite Exponent Boundary

The final finite exponent boundary asks for two fields:

```text
D.exponentMinimum =
  aoyagiTheorem2Lambda_fromCeilData L (n+1) H r m data

D.exponentOrder = data.theorem2OrderFormula.
```

If the minimum field is supplied, and the chart/order calculation gives

```text
D.exponentOrder = TC.terminalMinimumLabels.card,
```

then the order field follows by transitivity:

```text
D.exponentOrder
  = TC.terminalMinimumLabels.card
  = data.theorem2OrderFormula.
```

The active-ratio variants are the same calculation after using the existing
finite certificate

```text
D.exponentMinimum_eq_of_activePair_ratioAt_eq_of_forall_le.
```

The chart-count variants first use the existing finite max certificate

```text
D.exponentOrder_eq_of_chart_minCount_eq_of_forall_le
```

or the displayed-ratio count rewrite

```text
D.exponentOrder_eq_of_countInChartAtRatio_eq_of_forall_le.
```

After those certificates produce

```text
D.exponentOrder = TC.terminalMinimumLabels.card,
```

the same transitivity with the exact terminal count fills the order field.

## Final Boundary

The supplied final boundary and chart-final boundary add only the already
existing selected-width provenance and normal-crossing extraction hypothesis.
They do not change the finite calculation above.

## Nonclaims

- No source construction of Eq5 endpoint families.
- No A5 classifier, back-to-label, injectivity, or no-extra source proof.
- No global normal-crossing chart production or chart coverage.
- No active-ratio lower-bound proof.
- No displayed-ratio chart-count proof.
- No Case 1 or Case 2 source-production progress.
- No Aoyagi Lemma 1, Theorem 4, regular-coordinate additivity, or analytic
  ideal-transport citation.
- No pole-order or RLCT theorem beyond the already explicit
  normal-crossing extraction hypothesis.
