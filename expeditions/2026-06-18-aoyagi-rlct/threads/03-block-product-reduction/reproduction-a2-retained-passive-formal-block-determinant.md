# A2 retained-passive formal block determinant

Status: controller reproduced; Lean-proved; review pending.

## Scope

This note records the finite block-order determinant calculation that sits
between the edge-local `(F,C)` pair determinant and the eventual explicit
raw-order derivative determinant for `topologyTupleEdgeRawOrder`.

It is deliberately formal.  The theorem is not an analytic `fderiv` theorem,
not a proof that the formal block map is the derivative of the raw tuple map,
not a source-prior pushforward, not a measure theorem, not normal crossings,
and not RLCT extraction.

## Block variables

The determinant-friendly tangent order is

```text
(passive A1 blocks,
 passive A3 blocks,
 Ctop solve block,
 edge-local (F_p,C_p) blocks for p : Fin (M+1),
 terminal F3 solve block).
```

This is not the literal `TopologyTuple` product order.  A later raw-order
theorem must account for the permutation between these orders.  The signed
determinant may pick up a permutation sign; the absolute determinant does not.

## Factors

Let

```text
Tail    : Matrix rho rho K
A p     : Matrix rho rho K
H p     : Matrix rho (kappa' p.succ) K
G p     : Matrix (kappa' p.succ) rho K
LastTop : Matrix rho rho K.
```

The formal block map is the product map of:

```text
id on passive A1,
id on passive A3,
Ctop |-> Tail^{-1} * Ctop,
product_p edgeLocalFCPairLinearMap (A p) (H p) (G p),
F3 |-> F3 * (-LastTop).
```

The already proved edge-local determinant gives

```text
det edge_p = det(-A p)^(|kappa' p.castSucc|).
```

Left and right multiplication contribute

```text
det(Ctop |-> Tail^{-1} * Ctop)
  = det(Tail^{-1})^(|rho|)

det(F3 |-> F3 * (-LastTop))
  = det(-LastTop)^(|kappa' (Fin.last (M+1))|).
```

The identity and product bookkeeping then gives the signed determinant in the
chosen block order:

```text
det =
  det(Tail^{-1})^(|rho|)
  * product_{p : Fin (M+1)} det(-A p)^(|kappa' p.castSucc|)
  * det(-LastTop)^(|kappa' (Fin.last (M+1))|).
```

## Endpoint check

The formal determinant theorem keeps `LastTop` as an independent matrix
parameter.  When it is instantiated by the terminal residual-factor product
used by the solved lower-left block, that one-edge product at the end of the
chain satisfies:

```text
residualFactorProduct A
  (Fin.last (M+1)) (Fin.last M).castSucc
  (Fin.last M).castSucc.le_last
= A (Fin.last M).
```

This matters in the single-edge case: for `M = 0`, the first-edge tail is
empty, but the terminal residual-product instance of `LastTop` is `A 0`, not
`1`.

## Lean status

Generic determinant helpers added to
`lean/DLNFibre/DLN/Aoyagi/MatrixLinearDeterminant.lean`:

```text
moduleFinite_pi
Matrix.det_blockDiagonal'
linearMap_det_piMap_eq_prod
```

Formal retained-passive block determinant added in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveFormalLinearDeterminant.lean`:

```text
RetainedPassiveFormalEdgeTangent
edgeLocalFCPairPiLinearMap
edgeLocalFCPairPiLinearMap_det_eq
RetainedPassiveTotalFormalBlockTangent
retainedPassiveTotalFormalBlockJacobian
retainedPassiveTotalFormalBlockJacobian_det_eq
retainedPassiveLastTopResidualFactorProduct_eq
```

The new module is imported by `lean/DLNFibre.lean`.

## Remaining bridge

The next mathematical bridge is to connect this formal block-order determinant
to the actual derivative of `topologyTupleEdgeRawOrder`.  That requires:

- identifying the block-order formal coordinates inside the raw tuple order;
- proving the extra dependencies are determinant-one shears or translations;
- accounting for the product-coordinate permutation sign for signed
  determinants, or passing directly to the absolute determinant formula.
