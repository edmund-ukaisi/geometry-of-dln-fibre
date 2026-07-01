# Review - A2 Case 2 passive-theta raw-order reference

Date: 2026-07-01.

Status: controller pre-Lean review.

## Checks

- The raw-order reference is defined as an actual image measure of the
  concrete theta-domain reference source.
- The target support set is
  `topologyTupleRawOrderSourceRecursiveDetChartSet`, not unrestricted raw
  Haar.
- The proof must shrink through the existing determinant/punctured-sector
  theorem, because `topologyTupleEdgeRawOrder` is used through its
  determinant-chart continuity API.
- The nonzero selected-entry pivot is required only by the local
  raw-order/source-chart package; determinant support alone would not need it.
- Passive-field domination is transported by first taking product with the
  same weighted center box, then restricting to `V`, then mapping by the
  locally a.e. measurable raw map.
- The theorem must not state image equality with full Haar or a full
  coordinate-volume chart.

## Boundary

This is a raw-image support and domination layer.  It is a safe downstream
consumer of the endpoint reference measure and the raw-order/source-chart
package, but it does not solve the missing source-prior or source-rank
coverage problems.
