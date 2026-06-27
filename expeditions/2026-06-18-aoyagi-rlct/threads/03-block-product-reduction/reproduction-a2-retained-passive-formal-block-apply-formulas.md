# A2 retained-passive formal block apply formulas

Status: controller reproduced; Lean-proved; review pending.

## Scope

This note records the blockwise value formulas for the formal retained-passive
Jacobian introduced for the p.13 determinant calculation.  These formulas are
the comparison target for a later theorem relating the formal block map to the
actual derivative of `topologyTupleEdgeRawOrder`.

This is still only finite linear algebra.  It is not yet an analytic
`fderiv` theorem, not a product-coordinate permutation theorem, not measure
transport, not normal crossings, and not RLCT extraction.

## Edge-local product

For every edge `p : Fin (M+1)`, the dependent product of edge-local maps sends
the edge tangent pair `(dF_p, dC_p)` to

```text
(-(A p + H p * G p) * dF_p + H p * dC_p,
 -G p * dF_p + dC_p).
```

This is exactly the linear part of the retained-passive raw block formulas
for `(Y12_p, Y22_p)` once the earlier `(Y11_p, Y21_p)` coordinates are treated
as already exposed block variables.

Lean theorem:

```text
edgeLocalFCPairPiLinearMap_apply
```

## Total block-order map

For a block tangent vector

```text
v =
  (dA1passive,
   (dA3passive,
    (dCtop,
     (dEdge, dF3))))
```

the formal block map sends `v` to

```text
(dA1passive,
 (dA3passive,
  (Tail^{-1} * dCtop,
   (p |-> edgeLocalFCPairLinearMap (A p) (H p) (G p) (dEdge p),
    dF3 * (-LastTop)))))
```

and the edge component expands to

```text
p |->
  (-(A p + H p * G p) * (dEdge p).1 + H p * (dEdge p).2,
   -G p * (dEdge p).1 + (dEdge p).2).
```

Lean theorems:

```text
retainedPassiveTotalFormalBlockJacobian_apply
retainedPassiveTotalFormalBlockJacobian_edge_apply
```

## Orientation checks

- The `Ctop` block is left multiplication by `Tail^{-1}`.
- The terminal `F3` block is right multiplication by `-LastTop`, so the value
  formula is `dF3 * (-LastTop)`.
- The edge block keeps the sign inside `-(A p + H p * G p)` and `-G p`, in
  the same `(F,C)` to `(Y12,Y22)` orientation as the proved edge-local
  determinant theorem.

## Remaining bridge

The next bridge must identify these block variables inside the raw
`TopologyTuple` derivative and show that the extra cross terms are
determinant-one shears or translations, with only a product-coordinate
permutation sign left for signed determinants.
