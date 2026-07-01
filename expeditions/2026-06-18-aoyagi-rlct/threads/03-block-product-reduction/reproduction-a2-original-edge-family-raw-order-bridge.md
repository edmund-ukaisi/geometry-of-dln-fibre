# Reproduction - A2 Original Edge-Family Raw-Order Bridge

Date: 2026-07-01.

Status: pen-and-paper check before Lean. This is a finite coordinate bridge
from retained-passive raw-order tuples to original edge-family tuple
coordinates. It is not a measure transport theorem.

## Question

The retained-passive raw-order tuple stores the edge blocks in the product
order

```text
A1passive, F2, A3passive, C, Ctop, F3.
```

Can this full raw tuple space be identified linearly with the original matrix
tuple coordinate space once Aoyagi's p.13 endpoint basis indices

```text
I_j := Fin (finrank U0) ⊕ κ'_j
```

are renamed by finite equivalences `e_j : I_j ≃ Fin (d_j)`?

## Calculation

For a raw tuple `y`, define the raw edge matrix at edge `p` by reassembling
the four displayed blocks:

```text
E_p(y) =
  Matrix.fromBlocks
    A1_p(y)  F2_p(y)
    A3_p(y)  C_p(y).
```

Here the top-left and lower-left blocks use the endpoint convention already
encoded by `rawEdgeTupleA1` and `rawEdgeTupleA3`: edge `0` reads `Ctop` as its
top-left block, interior top-left blocks read `A1passive`; terminal lower-left
reads `F3`, and earlier lower-left blocks read `A3passive`.

Thus `y ↦ E(y)` is a finite product linear equivalence between raw tuples and
edge-family matrices. Its inverse reads the four blocks back from each edge
matrix.  The identities are blockwise:

```text
edgeFamilyRawOrderTuple (edgeFamilyOfRawOrderTuple y) = y
edgeFamilyOfRawOrderTuple (edgeFamilyRawOrderTuple E) = E.
```

Now let `e_j : ρ ⊕ κ'_j ≃ Fin (d_j)` be arbitrary finite equivalences. Define
the original tuple coordinate readout by edgewise row/column reindexing:

```text
R_e(y)_p := Matrix.reindex (e_{p.succ}) (e_{p.castSucc}) (E_p(y)).
```

The inverse sends a tuple `A` to edge matrices

```text
E_p := Matrix.reindex (e_{p.succ})^{-1} (e_{p.castSucc})^{-1} (A_p),
```

then unpacks the blocks into raw tuple order.  Since `Matrix.reindex` is a
linear equivalence and finite products of these maps are linear equivalences,
`R_e` is a global linear equivalence on the full ambient raw tuple space.
The continuity is entrywise continuity of finite coordinate projections and
matrix `submatrix`/`fromBlocks`.

For the p.13 fixed endpoint bases, specialize

```text
ρ := Fin (finrank U0)
κ' := throughSubspaceEndpointComplementIndex ...
d_j := card (Fin (finrank U0) ⊕ κ'_j)
e_j := Fintype.equivFin I_j.
```

On the raw-order source-recursive determinant chart, the existing p.13
readout theorem says the public raw-order source chart has fixed-basis edge
matrices exactly `E_p(y)`. Therefore the original edge-family matrix readout
in the reindexed p.13 bases is exactly `R_e(y)`. The determinant-chart
hypothesis is essential because the public source chart is defined by
readback through `topologyTupleEdgeRawOrderInverse`; it is not the global
linear map `R_e`.

## Lean Target

Add:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyRawOrderBridge.lean

edgeFamilyTupleReindexLinearEquiv
rawOrderMatrixTuple
rawOrderMatrixTupleLinearEquiv
edgeFamilyTupleReindexContinuousLinearEquiv
rawOrderMatrixTupleContinuousLinearEquiv
paperEndpointFixedBaseRawOrderMatrixTupleLinearEquiv
paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
edgeFamilyMatrixTuple_p13Basis_reindex_rawOrderSourceChart_eq_rawOrderMatrixTuple
edgeFamilyMatrixTuple_p13FinBasis_rawOrderSourceChart_eq_rawOrderMatrixTuple
```

## Kill Conditions

- If `edgeFamilyOfRawOrderTuple` is only a chart-local inverse rather than the
  full block reassembly inverse to `edgeFamilyRawOrderTuple`, the global
  equivalence claim is false.
- If `Matrix.reindex` is used in the wrong row/column direction, the p.13
  bridge silently transposes the coordinate convention.
- If the p.13 source-chart readout theorem is used without
  `topologyTupleRawOrderSourceRecursiveDetChartSet`, the public nonlinear
  chart has been overextended.

## Nonclaims

No theorem here says that a restricted determinant-chart measure, source-chart
measure, or chart pushforward is Haar. No theorem compares
`originalEdgeFamilyVolume` with the retained-passive chart-produced measure.
No theorem proves a Jacobian formula, source-rank coverage, normal crossings,
pole order, or RLCT extraction.
