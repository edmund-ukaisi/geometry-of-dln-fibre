# Review - A2 with-following determinant/raw-order transport

Date: 2026-07-02.

Reviewer: `Ramanujan the 2nd`, xhigh read-only subagent.

## Scope

Reviewed the two new Lean declarations:

```text
exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_baseJ_restrict_le_smul_rawHaar_restrict_rawSource_of_endpointTopologyTuple_restrict_le_smul_detHaar
exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_baseJ_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple
```

and the reproduction/statement notes:

```text
reproduction-a2-with-following-forward-det-to-raw-domination.md
reproduction-a2-with-following-reverse-det-to-raw-domination.md
statement-card-a2-with-following-determinant-raw-order-transport.md
```

## Findings

None.

## PASS

The reviewer checked that the forward and reverse inequalities are oriented
correctly:

```text
Measure.map Y (sourceMeasure.restrict V)
  <= c * rawHaar.restrict rawDetChart
```

transports to raw domination, while:

```text
rawHaar.restrict rawDetChart
  <= c * Measure.map Y (sourceMeasure.restrict V)
```

transports to reverse raw-source domination.

The reviewer also checked that the formal retained-passive density is placed on
the determinant side before pushing by `topologyTupleEdgeRawOrder`, and that
both proofs use the retained-passive product COV theorem directly.

The theorems were judged genuinely independent of the non-following
passive-product/source-prior machinery: both quantify an arbitrary
`sourceMeasure`, with no `passiveMeasure`, `Rres`, weighted box, or reference
prior input.  The only local geometric input is the with-following source-chart
shrink/readback package, used for determinant-chart membership and raw-chart
bookkeeping.

Boundary language was judged accurate: determinant-side domination remains a
hypothesis, and no source-prior transport, exact raw-Haar pushforward, coverage,
normal crossings, pole order, or RLCT extraction is claimed.
