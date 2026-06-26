# Review - A2 retained-passive transformed-edge readbacks

Date: 2026-06-26.

Reviewer: xhigh read-only reviewer `Planck the 3rd`.

## Scope

Audit the current retained-passive transformed-edge readback rung in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`:

```text
ChartLocalSuffixState.retainedPassiveTransformedEdge_readbacks
ChartLocalSuffixState.retainedPassiveFixedBaseEdgeMatrices_transformedEdge_readbacks
```

The review checked the sign/order convention, the upper-right chart readback,
the Schur residual convention, and the fixed-base corollary against
`reproduction-a2-retained-passive-transformed-edge-readbacks.md`.

## Verdict

PASS.

## Checks

The retained-passive transformed edge is exactly

```text
[ A1_p       -A1_p * F2_p
  A3_p        C_p - A3_p * F2_p ].
```

The direct block projections read back `A1_p`, `-A1_p*F2_p`, and `A3_p`.  The
upper-right chart coordinate has the correct sign:

```text
-A1_p^-1 * (-(A1_p * F2_p)) = F2_p,
```

using `IsUnit det(A1_p)` to cancel `A1_p^-1*A1_p`.

The Schur residual uses the project convention

```text
lowerRight - lowerLeft * topLeft^-1 * upperRight,
```

so the displayed block gives `C_p`.

The fixed-base theorem is only the expected corollary obtained by rewriting the
deterministic transformed edge with
`retainedPassiveFixedBaseEdgeMatrices_transformedEdge_eq`.

## Nonclaims

The reviewed Lean does not define a bundled coordinate domain and does not
prove a two-sided local inverse.  It proves no source coverage, source/image
equality, source-measure pushforward, density/Jacobian theorem, normal
crossings, pole order, or RLCT extraction.
