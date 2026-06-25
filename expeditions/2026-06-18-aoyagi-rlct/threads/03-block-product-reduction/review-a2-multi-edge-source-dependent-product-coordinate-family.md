# Review - A2 multi-edge source-dependent product-coordinate family

Date: 2026-06-25.

Scope: pointwise source-dependent multi-edge product-coordinate family and
component coordinate identities.

## Verdict

Accepted at the pointwise finite-coordinate scope.  The theorem specializes
the fixed-`Ebase` constructor to the base edge matrices of `CedgeBase x` and
proves the component identities needed by the existing product-coordinate
shape socket.

## Checks

- `Ebase(x)` is built with
  `paperEndpointFixedBaseEdgeMatrixOfReverseEdges` applied to
  `(CedgeBase x p : _ ->L[_] _)`.
- The product family uses the base transformed Schur residual blocks
  `residualBlock(Ebase(x), last, p)`, not raw lower-right blocks.
- The residual identity is proved by comparing both sides to
  `value(residualProduct(Ebase(x), last, 0))`.
- The regular identity keeps the literal Euclidean coordinate vector `u`; no
  hidden sign or linear coordinate change is introduced.
- The determinant-unit hypothesis is exactly `IsUnit(det(Ctop(u)))`.

## Boundary

The theorem is multi-edge and pointwise.  It should not be used as a
continuity theorem, determinant-neighborhood theorem, product chart, source
coverage result, measure-transport theorem, normal-crossing certificate, pole
order theorem, or RLCT extraction.
