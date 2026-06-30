# Statement Card - A2 p.13 Fixed-Basis Original Coordinate Readout

## Claim

Aoyagi's p.13 fixed endpoint bases, whose index at vertex `j` is

```text
Fin (finrank U0) ⊕ κ'_j,
```

can be reindexed to bases over `Fin (d j)`. With these reindexed bases, the
original edge-family coordinate map `edgeFamilyMatrixTuple` is exactly the
p.13 fixed-base edge-matrix map, with each edge matrix reindexed by the same
finite equivalences. The canonical specialization uses
`d j = card (Fin (finrank U0) ⊕ κ'_j)` and `Fintype.equivFin`. For the
retained-passive raw-order source chart, this specializes to the existing
`edgeFamilyOfRawOrderTuple` readout, again with only finite row/column
reindexing.

Public Lean names:

```text
paperEndpointFixedBaseCoordinateIndex
paperEndpointFixedBaseDim
paperEndpointFixedBaseFinBasis
edgeFamilyMatrixTuple_p13Basis_reindex_eq
edgeFamilyMatrixTuple_p13Basis_reindex_rawOrderSourceChart_eq
edgeFamilyMatrixTuple_p13FinBasis_eq_reindex_edgeMatrix
edgeFamilyMatrixTuple_p13FinBasis_rawOrderSourceChart_eq
```

## Inputs Used

- finite-dimensional real vector spaces in the reversed Aoyagi chain;
- the fixed base paper-order chain `B`;
- a complement `U0` to the kernel of the endpoint total map;
- Aoyagi's fixed endpoint basis
  `paperEndpointFixedBaseBasis W B U0 hU0`;
- finite equivalences
  `e j : paperEndpointFixedBaseCoordinateIndex W B U0 j ≃ Fin (d j)`;
- for the raw-order specialization, membership of `y` in
  `topologyTupleRawOrderSourceRecursiveDetChartSet`.

## Output

The generic edge-family readout is:

```text
edgeFamilyMatrixTuple
    (fun j => (paperEndpointFixedBaseBasis W B U0 hU0 j).reindex (e j)) E
  =
fun p =>
  Matrix.reindex (e p.succ) (e p.castSucc)
    (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U0 hU0 E p).
```

The canonical Fin-indexed dimension and basis are:

```text
paperEndpointFixedBaseDim W B U0 j

paperEndpointFixedBaseFinBasis W B U0 hU0 j
  : Basis (Fin (paperEndpointFixedBaseDim W B U0 j)) ℝ (reverseVertex W j)
```

and the same formula holds with `e j = Fintype.equivFin (...)`. The raw-order
source-chart theorem rewrites the p.13 edge matrix as
`edgeFamilyOfRawOrderTuple y p`.

## Proof Shape

The generic theorem is entrywise:

```text
LinearMap.toMatrix (b_from.reindex e_from) (b_to.reindex e_to) f i j
  =
LinearMap.toMatrix b_from b_to f (e_to.symm i) (e_from.symm j).
```

This is exactly `Matrix.reindex e_to e_from` of the p.13 edge matrix. The
raw-order theorem rewrites the p.13 edge matrix by the existing theorem
`paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13RawOrderSourceChart_eq`.

## Nonclaims

This is a coordinate-readout bridge only. It does not prove that the original
edge-family volume equals, dominates, or is dominated by any chart-produced
source-image measure. It does not prove Haar normalization, Jacobian
transport, source-rank coverage, normal crossings, pole order, or RLCT
extraction.
