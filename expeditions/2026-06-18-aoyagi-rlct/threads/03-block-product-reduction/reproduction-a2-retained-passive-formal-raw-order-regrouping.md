# A2 retained-passive formal raw-order regrouping

Status: controller reproduced; Lean-proved; review pending.

## Scope

This note records the product-coordinate regrouping between the
determinant-friendly formal block order and the raw retained-passive
`TopologyTuple` order.  It is only finite linear algebra and product
bookkeeping.  It is not yet an analytic derivative theorem for
`topologyTupleEdgeRawOrder`, not measure transport, not normal crossings, and
not RLCT extraction.

The Lean theorem is stated over a commutative ring with finite index types.
The notation `Tail^{-1}` below denotes Lean's total matrix inverse.  On the
eventual determinant chart this will coincide with ordinary inverse after the
needed invertibility/unit hypotheses are connected, but those hypotheses are
not part of this purely formal regrouping theorem.

## Orders being compared

The formal block determinant calculation uses the order

```text
(A1passive, A3passive, Ctop, edge(F2,C), F3).
```

Here `edge(F2,C)` is the dependent family

```text
p |-> (dF2_p, dC_p).
```

The retained-passive raw `TopologyTuple` order is

```text
(A1passive, F2, A3passive, C, Ctop, F3).
```

The regrouping map `e` sends

```text
(a1, (a3, (ctop, (edge, f3))))
```

to

```text
(a1,
 (p |-> (edge p).1,
  (a3,
   (p |-> (edge p).2,
    (ctop, f3)))))
```

and its inverse sends

```text
(a1, (f2, (a3, (c, (ctop, f3)))))
```

to

```text
(a1,
 (a3,
  (ctop,
   (p |-> (f2 p, c p), f3)))).
```

Lean definitions:

```text
RetainedPassiveRawTopologyTuple
retainedPassiveFormalEdgeTangentLinearEquiv
retainedPassiveFormalBlockToRawTopologyTupleLinearEquiv
```

## Transported formal raw-order map

Let `L` be the already-proved formal block-order Jacobian

```text
retainedPassiveTotalFormalBlockJacobian Tail A H G LastTop.
```

The raw-order formal map is defined by conjugation:

```text
e * L * e.symm
```

in Lean as

```text
retainedPassiveFormalRawOrderJacobian Tail A H G LastTop.
```

For a raw tuple

```text
z = (dA1, (dF2, (dA3, (dC, (dCtop, dF3)))))
```

the transported formal map sends `z` to

```text
(dA1,
 (p |-> -(A p + H p * G p) * dF2 p + H p * dC p,
  (dA3,
   (p |-> -G p * dF2 p + dC p,
    (Tail^{-1} * dCtop,
     dF3 * (-LastTop))))))
```

Lean theorem:

```text
retainedPassiveFormalRawOrderJacobian_apply
```

## Determinant check

Since the raw-order formal map is exactly a linear conjugate of the formal
block-order map, its signed determinant is the same as the block-order signed
determinant.  No separate permutation sign computation is needed for this
transported formal map.

The determinant is

```text
det(Tail^{-1}) ^ card rho
*
(prod p : Fin (M+1), det(-A p) ^ card (kappa' p.castSucc))
*
det(-LastTop) ^ card (kappa' (Fin.last (M+1))).
```

Lean theorem:

```text
retainedPassiveFormalRawOrderJacobian_det_eq
```

## Remaining bridge

This does not assert that the analytic derivative of the raw coordinate map is
literally this transported formal map.  A later analytic bridge should compare
`fderiv topologyTupleEdgeRawOrder` with this formal raw-order map and isolate
any extra dependence on already-exposed variables.  The expected route is via
determinant-one shears or translation terms, but that comparison is outside
this slice.
