# Review - A2 Case 2 determinant-chart selected-entry residual handoff

Reviewer: Russell, xhigh read-only review.

Status: PASS.

## Scope

Reviewed the Case 2 specialization theorem

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  retainedPassiveP13Canonical_detChart_residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_selectedEntrySignedBox_map
```

against the relevant retained-passive and selected-entry APIs.

## Checks

- The chart measurability route is correct.  The theorem keeps the required
  target `BorelSpace` instance and proves continuity of the chart by composing
  continuity of the selected-entry retained-passive data, endpoint transport,
  and `topologyTuple`; continuity then gives a.e. measurability.
- `directChart (chart y)` matches the Case 2 source family used by the
  residual readout.  The simplification is by unfolding together with
  `ofTopologyTuple_topologyTuple`.
- The original reviewed version kept the determinant-chart pushforward
  identity and target positive-set measurability explicit.  The later
  direct-chart positive-set measurability hardening discharges the latter
  internally for this Case 2 specialization; the determinant-chart pushforward
  identity remains explicit.
- No source-prior, Jacobian comparison, chart-coverage, normal-crossing,
  pole-order, or RLCT statement is claimed.

## Verification Note

The reviewer did not run Lean commands.  The controller separately ran the
focused build and gates recorded in the statement card.
