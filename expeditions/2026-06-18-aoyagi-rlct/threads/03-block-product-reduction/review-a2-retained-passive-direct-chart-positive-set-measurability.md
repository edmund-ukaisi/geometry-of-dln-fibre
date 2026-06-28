# Review - A2 retained-passive direct-chart positive-set measurability

Reviewer: Kant, xhigh read-only review of the reproduction note.

Status: PASS, with Lean-surface caveat addressed.

## Checks

- The mathematical scope is correct: the retained-passive source-edge-family
  readout identity is ambient, not determinant-chart restricted.
- The proof route is the right one: measurable edge matrices for
  `ofTopologyTuple z`, then
  `measurable_paperEndpointFixedBaseResidualBlockCoordinateMap_of_measurable_edgeMatrix`,
  then `measurableSet_residualSquareSum_pos_of_measurable`.
- The Lean implementation keeps the measurable-space assumptions on the
  `TopologyTuple` surface and uses a local Borel measurable-space instance for
  retained-passive data only inside the proof.
- The determinant-chart Case 2 wrappers now discharge the direct-chart
  positive-set measurability internally.

## Boundary

No determinant-chart pushforward identity, positivity, integrability, chart
coverage, original source-prior transport, local loss/density theorem, normal
crossing statement, pole order, or RLCT extraction is claimed.

## Verification

The controller ran focused builds of the topology, local Jacobian, and Case 2
local Jacobian modules after implementation.  Kant's review itself was
read-only and did not run builds.
