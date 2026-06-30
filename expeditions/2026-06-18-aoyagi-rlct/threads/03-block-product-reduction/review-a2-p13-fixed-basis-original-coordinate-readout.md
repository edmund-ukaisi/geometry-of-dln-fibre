# Review - A2 p.13 Fixed-Basis Original Coordinate Readout

Date: 2026-06-30.

Reviewer: xhigh sidecar `Hume the 2nd`.

## Verdict

PASS. No required changes.

## Checks

The Lean bridge only claims finite basis-index reindexing.  The module
docstring explicitly excludes measure, Jacobian, normal-crossing, and RLCT
consequences, and the public theorems are pure equalities of
`edgeFamilyMatrixTuple` with edgewise `Matrix.reindex`.

The row/column direction is correct.  `edgeFamilyMatrixTuple` uses
`LinearMap.toMatrix` with source basis `p.castSucc` and target basis `p.succ`.
The p.13 fixed-base edge matrix has rows indexed by `p.succ` and columns by
`p.castSucc`.  Therefore the bridge correctly uses:

```text
Matrix.reindex (e p.succ) (e p.castSucc)
```

The raw-order specialization keeps the determinant-chart membership
hypothesis `hy : y ∈ topologyTupleRawOrderSourceRecursiveDetChartSet`, matching
the imported p.13 raw-order readout theorem.

The reproduction and statement card have visible nonclaims.  The reviewer found
no hidden Haar, source-prior, measure-transport, domination, or RLCT overclaim.

## Reviewer Verification

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13Coordinates.lean
cd lean && lake env lean DLNFibre.lean
```
