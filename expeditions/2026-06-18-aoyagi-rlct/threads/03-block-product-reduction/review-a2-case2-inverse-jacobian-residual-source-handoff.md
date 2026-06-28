# Review - A2 Case 2 inverse-Jacobian residual-source handoff

Reviewer: Godel, xhigh read-only review.

Status: PASS.

## Scope

Reviewed the new Case 2 inverse-Jacobian handoff declarations:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  residualSourceHypotheses_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_case2EndpointTransport_selectedEntrySignedBox_map

PaperEndpointFixedBaseRegularCoordinateSourceData.
  exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_case2EndpointTransport_selectedEntrySignedBox_map
```

against the reproduction note, statement card, the Case 2 selected-entry
determinant-chart residual theorem, and the raw-order inverse-Jacobian sockets.

## Checks

- The declarations are in the requested namespace and their names match their
  content.
- The original reviewed version kept the determinant-chart pushforward
  identity, target positive-set measurability, `0 <= t`, positive radii, and
  selected-entry exponent inequality explicit.  The later direct-chart
  positive-set measurability hardening discharges target positive-set
  measurability internally; the determinant-chart pushforward identity remains
  explicit.
- The finite-integral theorem uses `0 < t`; the only weakening to `0 <= t` is
  `le_of_lt ht` for the selected-entry residual call, while the finite-integral
  socket receives `ht` directly.
- The docs and Lean comments do not claim determinant-chart pushforward proof,
  chart coverage, original prior transport, local loss/density proof,
  source-rank coverage, normal crossings, pole order, or RLCT extraction.

## Verification Note

The reviewer did not run builds.  The controller separately ran the focused
build and gates recorded in the statement card.
