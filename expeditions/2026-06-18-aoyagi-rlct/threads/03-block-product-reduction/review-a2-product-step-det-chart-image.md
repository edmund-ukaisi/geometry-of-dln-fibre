# Review - A2 product-step determinant-chart image

Date: 2026-06-26.

Verdict: accepted at the stated scope.

## Checks

- The forward `MapsTo` theorem uses the existing record-level preservation
  lemma `ProductReductionStepRawCoordinates.detChart_toChart`, avoiding a
  second determinant calculation.
- The surjectivity proof interprets a target raw-order tuple as a chart record
  before applying `toRaw`, avoiding the error of treating target tuples as raw
  source coordinates.
- The inverse round trip uses
  `productReductionStepCoordinate_right_inverse y hy.2 hy.1`; the hypothesis
  order is `A1` first, `Ctop` second.
- The image equality is proved directly from `MapsTo` and `SurjOn`.
- The strengthened Haar theorem is only a target rewrite of the previously
  landed weighted Haar theorem.

## Boundary

The theorem identifies the image of one determinant chart under the p. 13
coordinate change. It does not assert that these chart coordinates cover the
original DLN source, does not compare original prior densities, does not
remove the Jacobian density, and does not construct normal crossings or RLCT.
