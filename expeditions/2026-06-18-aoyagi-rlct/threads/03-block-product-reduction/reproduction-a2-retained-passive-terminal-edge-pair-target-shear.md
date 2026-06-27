# Reproduction - A2 retained-passive terminal edge-pair target shear

Date: 2026-06-27.

Status: controller pen-and-paper reproduction before Lean formalisation.

This is the terminal-edge packaging step after the terminal `F2` target shear.
It combines the terminal `F2` identity with the already-proved `C` unshear
identity, then reuses the formal `(F2,C)` inverse calculation.

## Setup

Let

```text
p = Fin.last M : Fin (M+1)
```

and write

```text
Dzv = d(topologyTupleEdgeRawOrder)_z(v),
coord = (ofTopologyTuple z).toCoordinateData.
```

Define the terminal normalized target pair by

```text
U_F = Dzv.F2_p + rawEdgeTupleA1(Dzv)_p * coord.F2 p.castSucc,
U_C = Dzv.C_p  + rawEdgeTupleA3(Dzv)_p * coord.F2 p.castSucc.
```

The landed terminal `F2` theorem gives

```text
U_F = formal.F2_p.
```

The landed `C` unshear theorem, valid for every edge and hence for
`p = Fin.last M`, gives

```text
U_C = formal.C_p.
```

Therefore the terminal normalized actual target pair equals the corresponding
formal raw-order output pair:

```text
(U_F, U_C) = (formal.F2_p, formal.C_p).
```

## Source Recovery

For a formal output pair `(formal.F2_p, formal.C_p)`, the previously reproduced
formal inverse is

```text
F_p = (coord.solvedA1 p)^-1 *
        (coord.F2 p.succ * formal.C_p - formal.F2_p),
C_p = formal.C_p + coord.solvedA3 p * F_p.
```

Substituting `formal.F2_p = U_F` and `formal.C_p = U_C` gives the terminal
actual target-side recovery formulas:

```text
(coord.solvedA1 p)^-1 * (coord.F2 p.succ * U_C - U_F)
  = v.F2_p,
```

and

```text
U_C + coord.solvedA3 p *
  ((coord.solvedA1 p)^-1 * (coord.F2 p.succ * U_C - U_F))
  = v.C_p.
```

No new inverse calculation is needed.  The determinant-chart hypothesis enters
only through the existing formal recovery theorem for `coord.solvedA1 p`.

## Boundary Cases

For `M = 0`, the single retained edge is terminal.  The successor slot
`p.succ` is `Fin.last (M+1)`, so `coord.F2 p.succ` is the terminal zero
coordinate.  The formulas still make sense: the terminal edge pair recovers
the unique source `F2` and `C` coordinates from the normalized actual target
pair.  This does not identify the terminal `F3` factor; there
`LastTop = coord.Ctop`, not `Tail`.

## Kill Conditions

- If the result is stated for nonterminal edges, it overclaims: nonterminal
  `F2` still contains a successor derivative term.
- If the recovery uses `Tail` or `LastTop` instead of `coord.solvedA1 p`, it is
  using the wrong edge-local diagonal factor.
- If the result is used as a determinant-one target-side equivalence, it
  overclaims; this is only a terminal component package.

## Nonclaims

No nonterminal staged target-side shear, no global determinant-controlled
linear equivalence, no actual derivative determinant formula, no measure
transport, no normal crossings, no pole order, and no RLCT follows from this
terminal edge-pair package alone.
