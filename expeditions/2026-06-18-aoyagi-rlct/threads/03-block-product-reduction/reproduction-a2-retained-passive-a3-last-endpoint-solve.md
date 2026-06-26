# Reproduction - A2 retained-passive `A3_last` endpoint solve

Date: 2026-06-26.

Status: pen-and-paper follow-up to
`reproduction-a2-retained-passive-l-tail-sum.md`.

## Setup

Use a nonempty retained-passive edge family with `M+1` edges, indexed by
`Fin (M+1)`, and `M+2` vertices, indexed by `Fin (M+2)`.  The final edge is
`lastEdge = Fin.last M`; its successor vertex is the terminal vertex.

The previous rung defined the explicit product tail by

```text
ProductTail_lastVertex = 0,
ProductTail_p =
  -(D_{p+1} * A3_p * Ctop_p^-1) + ProductTail_{p+1},
```

with the suffix fields read back as ordered products

```text
D_{p+1} = residualFactorProduct C terminal p.succ,
Ctop_p  = residualFactorProduct A1 terminal p.castSucc.
```

Here the `Ctop` product uses the constant top-index family `rho`.

## Last Edge

At the final edge `p=lastEdge`, the residual product from the terminal vertex to
itself is the identity:

```text
D_{last+1} = I.
```

The successor tail is the terminal tail, hence zero.  Therefore

```text
ProductTail_lastEdge
  = -(I * A3_last * Ctop_last^-1).
```

The displayed `I` is the terminal residual product; its type is indexed by
`(Fin.last M).succ`, definitionally the terminal vertex `Fin.last (M+1)`.
This is an indexing artifact, not an extra mathematical factor.

## Endpoint Cancellation

Let

```text
Ctop_last =
  residualFactorProduct A1 terminal lastEdge.castSucc.
```

Assume `det(Ctop_last)` is a unit.  If the final lower-left block is chosen as

```text
A3_last = -G * Ctop_last,
```

then the last tail is

```text
ProductTail_lastEdge
  = -(((-G * Ctop_last) * Ctop_last^-1))
  = -(-G * (Ctop_last * Ctop_last^-1))
  = -(-G * I)
  = G.
```

The cancellation uses right multiplication by the nonsingular inverse of
`Ctop_last`; no inverse of any residual `C` factor is introduced.

## Role in the Full Coordinate Inverse

This rung solves only the final summand for an arbitrary target `G`.  In the
full retained-passive coordinate-domain theorem, `G` should be instantiated as

```text
F3_0 + sum over p < lastEdge of
  D_{p+1} * A3_p * Ctop_p^-1,
```

so that the signed earlier tail contributions and the final tail sum to the
desired active source coordinate `F3_0`.

## Lean Scope

Main Lean names:

```text
retainedPassiveLowerLeftProductTailSum_last
retainedPassiveLowerLeftProductTailSum_last_eq_of_A3_eq_neg_target_mul_Ctop
```

The theorem is over a general commutative ring with finite matrix index types.
The determinant-unit hypothesis is explicit.  Lean's matrix inverse is total,
so the theorem is finite algebra; analytic chart uses still need determinant
unit propagation from the suffix-state `Ctop` chart.

## Nonclaims

This does not construct the retained-passive coordinate domain, does not build
the prefix target `G` from `F3_0` and the passive earlier-edge variables, does
not prove `A1_0` or `A3_last` are inside an open chart domain, and does not
prove source-rank coverage, source/image equality, measure pushforward,
density/Jacobian transport, normal crossings, pole order, or RLCT.
