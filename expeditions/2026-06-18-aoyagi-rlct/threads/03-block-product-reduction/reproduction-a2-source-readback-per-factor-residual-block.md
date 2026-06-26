# A2 source-readback per-factor residual block

## Boundary

This slice exposes a definitional source-readback field identity.  It does
not construct a source chart, endpoint equivalence, Case 2 displayed factor,
full-to-window transport, pivot nonzero fact, pushforward/Jacobian theorem,
original-loss comparison, normal crossing, pole order, or RLCT.

## Pen-and-paper reproduction

Fix a retained-passive-shaped source edge family

```text
E_p : rho + kappa_{p+1} -> rho + kappa_p
```

for `p = 0, ..., M`.  The suffix recursion defines the transformed edge seen
at step `p`:

```text
T_p = sourceReadbackTransformedEdge(E,p).
```

The retained-passive source readback is the coordinate tuple extracted from
these transformed edges.  Its residual factor field is defined by

```text
(sourceReadback E).C_p = schurResidualBlock(T_p).
```

Therefore, for every edge index `p`,

```text
(sourceReadback E).C p
  = schurResidualBlock(sourceReadbackTransformedEdge E p).
```

No determinant-chart hypothesis is needed for this equality: it is the field
definition of `sourceReadback.C`.

## Use

This theorem is a small API handle for source-specific factor-alignment work.
An adjacent-window Case 2 bridge can now cite the source-readback residual
factor at a chosen edge without unfolding all fields of `sourceReadback`.

## Kill conditions

- If this theorem is used to identify a Schur residual block with a displayed
  Case 2 post-pivot block, the displayed factor identity still has to be
  proved separately.
- If this theorem is used inside a full fixed-base endpoint product, outside
  factors or full-to-window transport still have to be accounted for.
- The theorem gives no pivot nonzero provenance and no analytic information.
