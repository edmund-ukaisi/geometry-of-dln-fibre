# Review - A2 Retained-Passive Local-Source Measurability

Date: 2026-06-26.

Reviewer: Lovelace the 3rd, xhigh.

Verdict: pass after documentation correction.

## Findings

The theorem statement and name are sound:

```text
measurableSet_paperEndpointFixedBaseRetainedPassiveP13LocalSource_of_continuous
```

states exactly measurability of the retained-passive local source under global
`Continuous Cedge` plus `OpensMeasurableSpace`.

The proof is exactly the intended topological argument: fixed-base edge-matrix
continuity, openness of `sourceRecursiveDetChartSet`, continuous preimage of
an open set, then open implies measurable.

Two stale documentation lines were corrected after review:

- the module header now mentions global-continuity measurability;
- the reproduction note status now says the Lean theorem has been formalised.

## Nonfindings

No false claim was found for source-rank openness, measure transport,
Jacobian, normal crossings, pole order, or RLCT.  The assumptions are adequate
for the theorem.  A weaker reusable variant could take continuity of the
fixed-base edge-matrix map directly, but the current wrapper matches the
global `Cedge` continuity target used in the expedition notes.
