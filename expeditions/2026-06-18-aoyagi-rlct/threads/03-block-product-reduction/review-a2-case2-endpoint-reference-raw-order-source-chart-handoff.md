# Review - A2 Case 2 endpoint-reference raw-order/source-chart handoff

Date: 2026-07-01.

Status: controller pre-Lean review.

## Checks

- The first identity is pure `map_map` after proving local a.e.
  measurability of `Phi` for the endpoint image.
- The second identity is the existing local two-stage raw-chart/source-chart
  equality instantiated with `referenceSource`.
- The theorem must keep `sourceChart` as a theta-domain map and use
  `rawChart o Phi` for endpoint-to-source transport.
- The theorem must not identify any image measure with raw Haar or
  determinant-chart Haar.
- The local nonzero pivot hypothesis is needed because this uses the
  raw-order/source-chart package.

## Boundary

This is a naming and functoriality handoff.  It prepares the endpoint
reference image for downstream raw-density/source-chart transport, but it
does not solve original prior transport or source-image coverage.
