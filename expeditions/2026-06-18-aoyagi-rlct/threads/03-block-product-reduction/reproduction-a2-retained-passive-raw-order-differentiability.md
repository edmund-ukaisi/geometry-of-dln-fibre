# Reproduction - A2 Retained-Passive Raw-Order Differentiability

Date: 2026-06-26.

Status: pen-and-paper reproduction for the first full raw-order derivative
foothold.  The Lean checkpoint proves differentiability only.  It does not
identify the derivative, prove a determinant formula, or state any measure or
RLCT consequence.

## Coordinate Setup

Write

```text
data(z) = ofTopologyTuple z,
A_p     = data(z).toCoordinateData.solvedA1 p,
L_p     = data(z).toCoordinateData.solvedA3 p,
F_i     = data(z).toCoordinateData.F2 i,
C_p     = data(z).toCoordinateData.C p.
```

The preceding checkpoints prove, on `topologyTupleDetChartSet`, that every
`z |-> A_p` and `z |-> L_p` is differentiable.  The stored fields
`z |-> F_i` and `z |-> C_p` are coordinate projections, with `F_i` using the
zero-filled `F2full` extension at the terminal index.

## Raw-Order Target Components

The raw block formulas already landed in
`RetainedPassiveCoordinatesTopology.lean`.  In tuple order, they say:

```text
A1passive target q =
  A_(q.succ) + F_(q.succ.succ) * L_(q.succ)

F2 target p =
  -(A_p * F_(p.castSucc))
    + F_(p.succ) * (C_p - L_p * F_(p.castSucc))

A3passive target q =
  L_(q.castSucc)

C target p =
  C_p - L_p * F_(p.castSucc)

Ctop target =
  A_0 + F_((0 : Fin (M+1)).succ) * L_0

F3 target =
  L_(Fin.last M).
```

These are exactly the components of `topologyTupleEdgeRawOrder z`.

## Differentiability Reproduction

The proof is componentwise over the product tuple.

For the top-left passive family, `A_(q.succ)` is differentiable by the
solved-`A1` theorem, `F_(q.succ.succ)` is differentiable by `F2full`
projection, and `L_(q.succ)` is differentiable by the solved-`A3` theorem.
Heterogeneous matrix multiplication gives differentiability of
`F_(q.succ.succ) * L_(q.succ)`, and addition gives the component.

For the `F2` family, the two summands are:

```text
-(A_p * F_(p.castSucc))
F_(p.succ) * (C_p - L_p * F_(p.castSucc)).
```

Each product is a rectangular matrix product, so the Lean proof uses
`differentiableAt_matrix_mul`, not scalar or square matrix ring `.mul`.
The inner residual `C_p - L_p * F_(p.castSucc)` is differentiable first, then
the outer product and sum are taken.

The lower-left passive and final `F3` components are direct solved-`A3`
projections.  The residual `C` family and `Ctop` component repeat the same
product/subtraction or product/addition arguments above.

Finally, the six component differentiability statements are assembled by
`differentiableAt_pi` for families and repeated `DifferentiableAt.prodMk` for
the nested `TopologyTuple` product.

## Lean Scope

The Lean checkpoint adds:

```text
differentiableAt_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
```

It uses the previous derivative ingredients:

```text
differentiableAt_solvedA1_of_mem_topologyTupleDetChartSet
differentiableAt_solvedA3_of_mem_topologyTupleDetChartSet
differentiableAt_F2full
differentiableAt_C
differentiableAt_matrix_mul
```

## Nonclaims

No formal derivative formula, tangent equivalence, determinant unit theorem,
Jacobian determinant formula, density, measure pushforward, image equality,
source-rank coverage, normal crossings, pole order, or RLCT statement is
proved here.

