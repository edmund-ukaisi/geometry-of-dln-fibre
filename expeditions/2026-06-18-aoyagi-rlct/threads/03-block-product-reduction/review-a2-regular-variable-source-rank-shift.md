# Review - A2 regular-variable source-rank shift

Date: 2026-06-24.

Reviewer: xhigh independent checker `Helmholtz the 2nd`.

## Verdict

Pass, narrowly.

## Review Summary

The checker confirmed that the slice is mathematically faithful when kept as
endpoint-bound plumbing.  Aoyagi p. 13 counts the regular block families
`C1 - Er`, `F2`, and `F3`; those sizes use the endpoint assumptions

```text
r <= H(1),
r <= H(L+1).
```

For the Lean specialization `L = N`, source-rank-stratum membership

```text
x in paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge
```

and the convention

```text
H(k+1) = finrank(W k)
```

legitimately give both endpoint bounds by applying

```text
paperEndpointFixedBaseSourceRankStratum_sourceRangeRankWidth W B hx hH
```

at `s=1` and `s=N+1`.

## Scope Check

The reviewer explicitly approved the current theorem shapes in
`RegularVariableShift.lean`:

```text
paperEndpointFixedBaseSourceRankStratum_regularVariableEndpointBounds
AoyagiNormalCrossingExponentData
  .exponentMinimum_jacobianPriorLossShift_regularVariableCount_of_sourceRankStratum
AoyagiNormalCrossingChartCertificate
  .exponentData_exponentMinimum_jacobianPriorLossShift_regularVariableCount_of_sourceRankStratum
AoyagiTheorem2FiniteExponentFormulaHypothesis
  .of_regularVariableCountShift_sourceRankStratum
AoyagiTheorem2FiniteExponentFormulaHypothesis
  .of_chart_regularVariableCountShift_sourceRankStratum
```

The names keep `sourceRankStratum` and `regularVariableCountShift` visible and
avoid claiming Theorem 3, analytic transport, or RLCT.

## Nonclaims

This slice does not prove Theorem 3 analytic transport, Aoyagi Lemma 1
normalization, exact-rank openness, regular-suspension chart construction,
ideal/RLCT invariance, normal crossings, pole order, or final RLCT extraction.
It also does not connect the supplied reduced certificate to the A2 geometry;
the reduced minimum/order hypotheses remain supplied.
