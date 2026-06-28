# Review - A2 Case 2 determinant-chart selected-entry chart-produced residual

Reviewer: Volta, xhigh read-only subagent.

Verdict: PASS.

The reviewer found no blocking mathematical or Lean-surface issue.  The scope
is correctly chart-produced and local: the claim does not remove the arbitrary
measure pushforward hypothesis from the existing theorem, and it does not claim
Haar transport, full determinant-chart coverage, source-prior identification,
source-rank coverage, normal crossings, pole order, or RLCT.

The planned support argument is sound: instantiate the supplied-map theorem
with `m = Measure.map chart weightedBox`, prove

```text
(Measure.map chart weightedBox).restrict Sdet = Measure.map chart weightedBox
```

from pointwise membership `chart y in Sdet`, and rewrite.  The needed Lean
interfaces are present:

- `case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_detChart`
  for determinant-chart membership of the endpoint-transported datum;
- `topologyTuple_mem_topologyTupleDetChartSet` for membership after applying
  `topologyTuple`;
- `withDensity_absolutelyContinuous` to move a.e. measurability from
  `signedBox` to `weightedBox`;
- `ae_map_iff` and `Measure.restrict_eq_self_of_ae_mem` for the support
  restriction.

Reviewer caveats recorded in the implementation:

- explicitly use `MeasurableSet Sdet`, supplied by
  `isOpen_topologyTupleDetChartSet.measurableSet`;
- keep the target `[BorelSpace (TopologyTuple ...)]` assumption;
- correct the statement-card exponent cast to `ℝ`.
