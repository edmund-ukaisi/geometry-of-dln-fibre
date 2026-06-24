# Review - Theorem 2 Source-Rank Regular-Shift Bridge

Date: 2026-06-24.

Reviewer: xhigh independent reviewer `Bernoulli the 3rd`.

## Verdict

Pass.  No blocking findings.

## Review Summary

The reviewer classified this as thin but useful composition, not misleading
wrapper churn, because the theorem keeps the analytic and finite obligations
explicit:

- the extraction hypothesis is required for the shifted certificate;
- the reduced finite minimum plus regular term remains supplied;
- the reduced finite order remains supplied.

The reviewer explicitly warned not to replace the shifted extraction hypothesis
by an unshifted `Cnc.ExtractionHypothesis`, since that would silently claim
analytic transport or regular-coordinate additivity.

## Approved Statement Shape

The chart theorem should keep:

```text
AoyagiDefinition3SourceData
  .exists_theorem2SuppliedChartFinalBoundary_of_sourceRankStratum_regularVariableCountShift
```

with inputs `S`, `hx`, `hH`,

```text
hNC :
  (Cnc.jacobianPriorLossShift
    (aoyagiTheorem2RegularVariableCount N H r)).ExtractionHypothesis
      lambda poleOrder,
```

and reduced supplied obligations:

```text
Cnc.exponentData.exponentMinimum + aoyagiTheorem2RegularTerm N H r
  = aoyagiTheorem2Lambda_fromCeilData ...

Cnc.exponentData.exponentOrder = data.theorem2OrderFormula.
```

The output should be exactly the shifted
`AoyagiTheorem2SuppliedChartFinalBoundary`, with the existing selected-width
side facts.  The non-chart finite-exponent-data analogue is also acceptable
when it uses the shifted `AoyagiNormalCrossingExtractionHypothesis`.

## Nonclaims

- No construction of `Cnc` or the shifted certificate.
- No regular-suspension construction.
- No analytic ideal transport or Aoyagi Lemma 1.
- No exact-rank openness.
- No normal-crossing chart production, active-ratio lower bound, or chart-count
  theorem.
- No pole-order/RLCT theorem beyond the explicitly supplied shifted extraction
  hypothesis.
- No proof that source-rank membership gives more than the rank-width and
  endpoint inequalities used by the finite shift.

## Limitation

The reviewer could not independently extract raw PDF text in this environment
because PDF text tools were unavailable, so the audit checked the reproduction
note and local Lean API surfaces.
