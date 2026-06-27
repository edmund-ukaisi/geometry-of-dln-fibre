# Reproduction - A2 retained-passive actual derivative passive A3 identity

Status: reproduced for the passive nonterminal lower-left coordinates.

This note is independent of the quiver-based paper. It uses only the
retained-passive block-coordinate algebra already isolated from Aoyagi's
p. 13 local product reduction.

## Coordinate calculation

In the retained-passive tuple order, the stored coordinates are

```text
(A1passive, F2, A3passive, C, Ctop, F3).
```

The raw edge tuple repacks the lower-left blocks by

```text
rawEdgeTupleA3 z (p.castSucc) = z.A3passive p,
rawEdgeTupleA3 z (Fin.last M) = z.F3.
```

For the forward retained-passive raw-order map, the lower-left edge block is
the solved lower-left family:

```text
rawEdgeTupleA3 (topologyTupleEdgeRawOrder z) q = coord.solvedA3 q.
```

At a passive index `p : Fin M`, the edge index is `p.castSucc`, not the
terminal edge. Hence `Fin.castSucc_ne_last p` applies, and the solved family
does not perform the terminal solve:

```text
coord.solvedA3 p.castSucc
  = coord.A3seed p.castSucc
  = z.A3passive p.
```

Therefore the passive lower-left component of the forward raw-order map is
literally the stored passive coordinate:

```text
(topologyTupleEdgeRawOrder z).A3passive p = z.A3passive p.
```

Taking the Frechet derivative in any tangent direction `v` gives

```text
((fderiv R topologyTupleEdgeRawOrder z) v).A3passive p = v.A3passive p.
```

The determinant-chart hypothesis is used only to access the already established
differentiability of the full raw-order map at `z`; the component identity
itself is elementary coordinate bookkeeping.

## Formal raw-order comparison

The transported formal raw-order Jacobian has apply formula

```text
(A1passive, F2, A3passive, C, Ctop, F3)
  |-> (..., ..., A3passive, ..., ..., ...).
```

Thus its passive lower-left component is also unchanged. Combining this with
the analytic identity above gives the passive `A3` component agreement between
the actual Frechet derivative and the point-specialized formal raw-order map.

## Nonclaims

This does not address the terminal lower-left `F3` coordinate. The terminal
coordinate is determinant-bearing and uses the solved endpoint formula. This
also does not prove a full analytic Jacobian determinant formula, an absolute
determinant equality, measure pushforward, normal crossings, pole order, or an
RLCT statement.
