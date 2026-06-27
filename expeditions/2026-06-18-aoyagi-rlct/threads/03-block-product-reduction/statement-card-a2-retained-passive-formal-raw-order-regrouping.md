# Statement card - A2 retained-passive formal raw-order regrouping

Status: Lean-proved; review pending.

## Claim

The determinant-friendly formal block order

```text
(A1passive, A3passive, Ctop, edge(F2,C), F3)
```

is linearly equivalent to the raw retained-passive `TopologyTuple` order

```text
(A1passive, F2, A3passive, C, Ctop, F3).
```

Conjugating the formal block-order Jacobian by this linear equivalence gives a
raw-order formal map with value formula

```text
(dA1,
 (p |-> -(A p + H p * G p) * dF2 p + H p * dC p,
  (dA3,
   (p |-> -G p * dF2 p + dC p,
    (Tail^{-1} * dCtop,
     dF3 * (-LastTop))))))
```

and determinant

```text
det(Tail^{-1}) ^ card rho
*
(prod p : Fin (M+1), det(-A p) ^ card (kappa' p.castSucc))
*
det(-LastTop) ^ card (kappa' (Fin.last (M+1))).
```

## Lean status

Proved in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveFormalRawOrder.lean`.

The theorem is stated over a commutative ring with finite index types, and
`Tail^{-1}` is Lean's total matrix inverse.  It becomes the ordinary inverse
only after the later determinant-chart invertibility hypotheses are supplied.

Definitions and theorems:

```text
RetainedPassiveRawTopologyTuple
retainedPassiveFormalEdgeTangentLinearEquiv
retainedPassiveFormalBlockToRawTopologyTupleLinearEquiv
retainedPassiveFormalRawOrderJacobian
retainedPassiveFormalRawOrderJacobian_apply
retainedPassiveFormalRawOrderJacobian_det_eq
```

## Caveat

This is still not the analytic derivative theorem for
`topologyTupleEdgeRawOrder`.  It is the formal raw-order comparison target for
the next derivative/shear bridge.
