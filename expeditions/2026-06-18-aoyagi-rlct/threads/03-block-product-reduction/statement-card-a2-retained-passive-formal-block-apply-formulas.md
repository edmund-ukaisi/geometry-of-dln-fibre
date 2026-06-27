# Statement card - A2 retained-passive formal block apply formulas

Status: Lean-proved; review pending.

## Claim

The dependent product of edge-local formal maps has component formula

```text
(dF_p, dC_p) |->
  (-(A p + H p * G p) * dF_p + H p * dC_p,
   -G p * dF_p + dC_p).
```

The total formal block-order map sends

```text
(dA1passive, dA3passive, dCtop, dEdge, dF3)
```

to

```text
(dA1passive,
 dA3passive,
 Tail^{-1} * dCtop,
 p |-> edgeLocalFCPairLinearMap (A p) (H p) (G p) (dEdge p),
 dF3 * (-LastTop)).
```

## Lean status

Proved in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveFormalLinearDeterminant.lean`.

Theorems:

```text
edgeLocalFCPairPiLinearMap_apply
retainedPassiveTotalFormalBlockJacobian_apply
retainedPassiveTotalFormalBlockJacobian_edge_apply
```

## Caveat

This is not yet the analytic derivative of `topologyTupleEdgeRawOrder`.  It is
the formal block-order map that the later raw-order derivative comparison
should reduce to, up to determinant-one shears/translations and coordinate
permutation signs.
