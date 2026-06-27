# Reproduction - A2 retained-passive nonterminal edge-pair staged target shear

Date: 2026-06-27.

Status: controller pen-and-paper reproduction before Lean formalisation.

This is the one-step nonterminal counterpart to the terminal edge-pair target
shear.  It is not yet a global descending construction.  The point is to
isolate the exact local calculation needed once the successor `F2` source
tangent has already been recovered by a later edge.

## Setup

Let `p : Fin M` and write the current retained edge as

```text
q = p.castSucc : Fin (M+1).
```

Then the successor retained edge is `p.succ : Fin (M+1)`, and the extended
successor slot used by `coord.F2` is `q.succ = p.castSucc.succ`.
In Lean this index is propositionally equal, not definitionally equal, to
`p.succ.castSucc`; the transport is along
`Fin.succ_castSucc p : p.castSucc.succ = p.succ.castSucc`.

Write

```text
Dzv = d(topologyTupleEdgeRawOrder)_z(v),
coord = (ofTopologyTuple z).toCoordinateData.
```

The already-landed all-edge `F2` shear identity gives

```text
Dzv.F2_q
  + rawEdgeTupleA1(Dzv)_q * coord.F2 q.castSucc
  - d(coord.F2 q.succ)(v) * coord.C q
= formal.F2_q.
```

The all-edge `C` unshear identity gives

```text
Dzv.C_q
  + rawEdgeTupleA3(Dzv)_q * coord.F2 q.castSucc
= formal.C_q.
```

For a nonterminal edge, the extended slot `coord.F2 q.succ` is the stored
source coordinate at the successor retained edge, transported along that
index equality.  Thus

```text
d(coord.F2 q.succ)(v)
  = cast_{p.succ.castSucc = p.castSucc.succ}(v.F2_(p.succ)).
```

This is the staged input: a descending construction may use the already
recovered successor source tangent, after this cast, in place of the displayed
derivative.

## Staged Normalized Pair

Given a supplied successor source tangent

```text
X_succ =
  cast_{p.succ.castSucc = p.castSucc.succ}(v.F2_(p.succ)),
```

define

```text
U_F =
  Dzv.F2_q
  + rawEdgeTupleA1(Dzv)_q * coord.F2 q.castSucc
  - X_succ * coord.C q,

U_C =
  Dzv.C_q
  + rawEdgeTupleA3(Dzv)_q * coord.F2 q.castSucc.
```

The projection derivative lemma identifies this `X_succ` with
`d(coord.F2 q.succ)(v)`.  Substitution into the `F2` shear identity and use of
the `C` unshear identity give

```text
(U_F, U_C) = (formal.F2_q, formal.C_q).
```

## Source Recovery

The formal edge-pair inverse at the current edge is

```text
F_q = (coord.solvedA1 q)^-1 * (coord.F2 q.succ * formal.C_q - formal.F2_q),
C_q = formal.C_q + coord.solvedA3 q * F_q.
```

Replacing `(formal.F2_q, formal.C_q)` by `(U_F, U_C)` yields the staged
nonterminal recovery formulas

```text
(coord.solvedA1 q)^-1 * (coord.F2 q.succ * U_C - U_F)
  = v.F2_q,
```

and

```text
U_C + coord.solvedA3 q *
  ((coord.solvedA1 q)^-1 * (coord.F2 q.succ * U_C - U_F))
  = v.C_q.
```

The determinant-chart hypothesis enters only through the existing formal
inverse theorem for `coord.solvedA1 q`.

## Boundary Cases

If `M = 0`, `Fin M` is empty, so there is no nonterminal edge.  The terminal
edge-pair package is the whole edge-pair construction.

If `q` is the edge immediately before the terminal edge, then the successor
tangent is `v.F2_(Fin.last M)`.  It is not zero; it is supplied by the
terminal edge-pair package.  The zero convention applies only one slot later,
to the terminal extended coordinate `coord.F2 (Fin.last (M+1))`.

The factor `coord.F2 q.succ` in the formal inverse is retained for every
nonterminal edge.  It must not be simplified away except in the terminal edge
case handled separately.

## Kill Conditions

- If `X_succ` is omitted from the nonterminal `F2` normalization, the formula
  misses the successor derivative term.
- If `X_succ` is set to zero before the terminal edge, the staged construction
  is wrong.
- If the dependent-index cast from the successor retained coordinate to the
  extended successor slot is omitted, the Lean theorem does not match the
  actual codomain of `coord.F2 q.succ`.
- If this one-step recovery is stated as a determinant equality or a
  determinant-one target-side equivalence, it overclaims.
- If the current edge is indexed directly by an arbitrary `q : Fin (M+1)`
  without a nonterminal hypothesis or `p : Fin M`, the statement risks
  conflating the terminal zero slot with a stored successor `F2` coordinate.

## Nonclaims

No full descending induction, no global target-side linear equivalence, no
determinant-one factorization, no actual derivative determinant formula, no
measure transport, no normal crossings, no pole order, and no RLCT follows
from this one-step staged recovery alone.
