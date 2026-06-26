# Review - A2 retained-passive fixed-base readback package

Date: 2026-06-26.

Reviewer: xhigh read-only reviewer `Lorentz the 3rd`.

## Scope

Audit the fixed-base retained-passive readback package in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`:

```text
ChartLocalSuffixState.retainedPassiveFixedBaseEdgeMatrix_activeEndpointAndEdgeReadbacks_eq_targets
```

The review checked endpoint signs, per-edge transformed-edge readback signs,
the solved `A1_0` and `A3_last` dependencies, and whether the statement
overclaims beyond finite fixed-base algebra.

## Verdict

PASS.

## Checks

The theorem is exactly a finite fixed-base package combining active endpoint
readbacks with per-edge transformed-edge readbacks.  The source-left endpoint
fields have the expected signs:

```text
-S_0.B = F2_0,
S_0.Ctop = Ctop,
lowerLeft(S_0.L) = F3.
```

The per-edge transformed-edge readback has the retained-passive sign
convention:

```text
upperRight(T_p) = -A1_p * F2_p,
-(A1_p^-1 * upperRight(T_p)) = F2_p.
```

The final lower-left endpoint solve uses

```text
A3_last = -(F3 - earlyTail) * CtopLast,
```

with right multiplication by `CtopLast`, as in the preceding endpoint package.

The full determinant-unit `A1` family is derived from passive units,
`det(Ctop)` unit, and the solved `A1_0 = Tail^-1 * Ctop` equation.  The
`A3_last` hypothesis is used only through the active endpoint package, and the
edge readbacks are supplied by
`retainedPassiveFixedBaseEdgeMatrices_transformedEdge_readbacks`.

## Nonclaims

The reviewed Lean does not define a bundled coordinate domain and does not
prove a two-sided local inverse.  It proves no source coverage, source/image
equality, source-measure pushforward, density/Jacobian theorem, normal
crossings, pole order, or RLCT extraction.
