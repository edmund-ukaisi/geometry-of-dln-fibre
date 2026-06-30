# Reproduction - A2 p.13 Fixed-Basis Original Coordinate Readout

Date: 2026-06-30.

Status: pen-and-paper check before Lean. This is a finite coordinate-index
bridge between Aoyagi's p.13 fixed endpoint bases and the expedition's
`originalEdgeFamilyVolume` coordinate convention. It is not a measure
transport theorem.

## Question

The original edge-family measure uses bases indexed by `Fin (d j)`. Aoyagi's
p.13 fixed endpoint bases are indexed instead by

```text
I_j := Fin (finrank U0) ⊕ κ'_j.
```

Can the fixed-base p.13 edge-matrix readout be put into the `Fin (d j)`
coordinate convention without changing the underlying basis vectors?

## Calculation

Let

```text
e_j : I_j ≃ Fin (d_j)
```

be any finite equivalence. Reindex the p.13 fixed endpoint basis
`b_j : Basis I_j ℝ V_j` by `e_j`:

```text
b^Fin_j := b_j.reindex e_j : Basis (Fin d_j) ℝ V_j.
```

For an edge family `E`, the original edge-family coordinate map reads

```text
M^Fin(E)_p =
  LinearMap.toMatrix (b^Fin_{p.castSucc}) (b^Fin_{p.succ}) E_p.
```

Expanding `Basis.reindex` and `LinearMap.toMatrix_apply`, the `(i,j)` entry is

```text
b_{p.succ}.repr (E_p (b_{p.castSucc}(e_{p.castSucc}^{-1} j)))
  (e_{p.succ}^{-1} i).
```

This is exactly `Matrix.reindex e_{p.succ} e_{p.castSucc}` of the p.13 edge
matrix

```text
LinearMap.toMatrix b_{p.castSucc} b_{p.succ} E_p.
```

Thus

```text
edgeFamilyMatrixTuple b^Fin E
  =
fun p =>
  Matrix.reindex e_{p.succ} e_{p.castSucc}
    (paperEndpointFixedBaseEdgeMatrixOfReverseEdges E p).
```

The canonical specialization sets

```text
d_j := card I_j,
e_j := Fintype.equivFin I_j.
```

On the raw-order retained-passive determinant chart, the existing p.13 readout
lemma gives

```text
paperEndpointFixedBaseEdgeMatrixOfReverseEdges (sourceChart y)
  = edgeFamilyOfRawOrderTuple y.
```

Substitution gives the specialized readout

```text
edgeFamilyMatrixTuple b^Fin (sourceChart y)
  =
fun p =>
  Matrix.reindex e_{p.succ} e_{p.castSucc}
    (edgeFamilyOfRawOrderTuple y p),
```

for `y` in the raw-order source-recursive determinant chart.

## Source Fidelity

Aoyagi p.13 works in fixed endpoint bases and writes edge maps as matrices in
those bases. The calculation above does not change the basis or the edge maps;
it only converts the finite index set from Aoyagi's displayed sum type to the
`Fin` index convention used by the original tuple measure. The raw-order
specialization uses the existing Lean theorem that the retained-passive p.13
source chart has edge matrices `edgeFamilyOfRawOrderTuple y`.

## Lean Target

Add:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13Coordinates.lean

paperEndpointFixedBaseCoordinateIndex
paperEndpointFixedBaseDim
paperEndpointFixedBaseFinBasis
edgeFamilyMatrixTuple_p13Basis_reindex_eq
edgeFamilyMatrixTuple_p13Basis_reindex_rawOrderSourceChart_eq
edgeFamilyMatrixTuple_p13FinBasis_eq_reindex_edgeMatrix
edgeFamilyMatrixTuple_p13FinBasis_rawOrderSourceChart_eq
```

## Kill Conditions

- If `Basis.reindex` changes the basis vectors rather than only renaming their
  index labels, the calculation is invalid.
- If `Matrix.reindex` is used in the wrong row/column direction, the theorem
  would silently reverse the coordinate convention.
- If the raw-order readout lemma holds only after additional source-chart
  hypotheses not present in the statement, the specialization is overstrong.

## Nonclaims

No theorem here identifies `originalEdgeFamilyVolume` with a retained-passive
or selected-entry chart-produced source-image measure. No theorem proves local
chart-piece equality, readback domination, Haar/Jacobian transport,
source-rank coverage, normal crossings, pole order, or RLCT extraction.
