# Review - A2 single-edge residual-product realisation

Date: 2026-06-25.

Reviewer mode: xhigh read-only scout checks by Dewey and Kierkegaard, followed
by controller integration.

## Verdict

Pass.

## Findings

Dewey checked the pen-and-paper calculation.  For

```text
[ Ctop,       -Ctop F2
  -F3 Ctop,   D + F3 Ctop F2 ],
```

the Schur residual is

```text
D + F3 Ctop F2 - (-F3 Ctop) Ctop^{-1} (-Ctop F2) = D
```

under `IsUnit Ctop.det`.  Dewey also checked that the theorem is independent
of the quiver/LR paper machinery and that it concerns the transformed Schur
residual product, not the raw lower-right block.

Kierkegaard checked Lean placement and proof shape.  The raw theorem belongs
after `suffixState_D_eq_residualProduct` in `ProductReduction.lean`, using
`suffixState_productCoordinate_fields_one` plus the `D = residualProduct`
bridge.  The fixed-base wrapper belongs immediately after
`paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean` in
`RegularSuspensionCoordinates.lean`.

## Risks Kept Explicit

- The determinant-unit hypothesis is necessary for the stated Schur residual
  cancellation.
- The theorem is single-edge only.
- The multi-edge arbitrary-terminal-residual question remains constrained by
  the intermediate-factor rank obstruction.
- No analytic, normal-crossing, pole-order, or RLCT claim follows from this
  finite algebra statement.
