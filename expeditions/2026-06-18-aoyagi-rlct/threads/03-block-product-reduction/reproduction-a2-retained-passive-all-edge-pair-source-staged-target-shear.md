# Reproduction - A2 retained-passive all-edge pair source-staged target shear

Date: 2026-06-27.

Status: controller pen-and-paper reproduction before Lean formalisation.

This packages the terminal edge-pair target shear and the one-step
nonterminal source-staged target shear into one retained-edge family.  It is
still only a family packaging lemma.  It is not a determinant statement and it
does not construct the later descending target-side change of variables.

## Setup

Work at a retained-passive raw tuple `z` in the determinant chart, with tangent
`v`.  Write

```text
raw = topologyTupleEdgeRawOrder,
coord = (ofTopologyTuple z).toCoordinateData,
Dzv = d(raw)_z(v),
formal = retainedPassiveFormalRawOrderJacobianAt(z)(v).
```

The retained `F2` and `C` edge families are indexed by `Fin (M+1)`.  The
successor source tangent family needed in the target-side normalization is

```text
Xsucc : forall q : Fin (M+1), Matrix rho (kappa' q.succ) R
Xsucc =
  Fin.snoc
    (fun p : Fin M =>
      cast_{p.succ.castSucc = p.castSucc.succ}(v.F2_(p.succ)))
    0.
```

Thus for a nonterminal edge `q = p.castSucc`, `Xsucc q` is the stored successor
source tangent, transported to the extended successor slot `q.succ`.  For the
terminal edge `q = Fin.last M`, `Xsucc q = 0`, matching the zero extension of
the retained-passive `F2` coordinate family one slot past the last retained
edge.

## Family Normalization

Define edge-family outputs

```text
U_F(q) =
  Dzv.F2_q
  + rawEdgeTupleA1(Dzv)_q * coord.F2 q.castSucc
  - Xsucc(q) * coord.C q,

U_C(q) =
  Dzv.C_q
  + rawEdgeTupleA3(Dzv)_q * coord.F2 q.castSucc.
```

We check the equality `(U_F, U_C) = (formal.F2, formal.C)` by splitting
`q : Fin (M+1)`.

If `q = Fin.last M`, then `Xsucc q = 0`, so

```text
U_F(q) =
  Dzv.F2_q + rawEdgeTupleA1(Dzv)_q * coord.F2 q.castSucc,
```

and `U_C(q)` is unchanged.  This is exactly the terminal edge-pair target
shear already proved, after simplifying the extra zero term.

If `q = p.castSucc` for `p : Fin M`, then

```text
Xsucc(q) =
  cast_{p.succ.castSucc = p.castSucc.succ}(v.F2_(p.succ)).
```

The one-step nonterminal source-staged theorem says precisely that the pair
`(U_F(q), U_C(q))` equals `(formal.F2_q, formal.C_q)`.

The two cases exhaust `Fin (M+1)`, including `M = 0`: when `M = 0` there are no
nonterminal `p`, and the sole retained edge is terminal.

## Source Pair Recovery

The formal raw-order `(F2,C)` map at a determinant-chart point is a linear
equivalence on separated edge families.  Its inverse recovers the source pair
from the formal pair:

```text
(formalEdgePairEquivAt z)^-1 (formal.F2, formal.C) = (v.F2, v.C).
```

Since the staged normalized family is equal to `(formal.F2, formal.C)`, the
same inverse recovers the whole retained source pair from `(U_F,U_C)`:

```text
(formalEdgePairEquivAt z)^-1 (U_F, U_C) = (v.F2, v.C).
```

This recovery is over all retained edges at once, but it is still the inverse
of the formal edge-pair block only.  It does not include the passive `A1`
block, the terminal `F3` block, or a determinant comparison for the actual
Frechet derivative.

## Kill Conditions

- If the edge immediately before the terminal edge is assigned zero successor
  tangent, the statement is wrong.  It must receive `v.F2_(Fin.last M)` with
  the dependent cast.
- If `Xsucc` is typed using `q.castSucc` instead of `q.succ`, it is not the
  successor term in the `F2` shear identity.
- If the terminal branch keeps a nonzero successor source tangent, it violates
  the retained-passive zero-extension convention.
- If the result is named or used as a determinant-one target-side linear
  equivalence, determinant formula, measure transport, normal-crossing
  theorem, pole-order theorem, or RLCT theorem, it overclaims.

## Nonclaims

No descending induction, no full target-side `LinearEquiv`, no determinant-one
shear, no actual derivative determinant formula, no measure transport, no
normal crossings, no pole order, and no RLCT follows from this packaging lemma.
