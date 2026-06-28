# Statement card - A2 Case 2 displayed product nonzero source production

## Claim

For the continuing Case 2 branch, a successor selected-entry coordinate vector
with nonzero displayed successor pivot coordinate determines constructed
finite displayed data whose post-pivot free two-edge product is exactly the
successor selected-entry matrix, and hence is nonzero.

This is a constructed-data theorem. It is not a theorem about an arbitrary
retained-passive `sourceReadback` point.

## Lean Artifacts

Files:

```text
lean/DLNFibre/DLN/Aoyagi/Case2ResidualFactorProduct.lean
lean/DLNFibre/DLN/Aoyagi/Case2ResidualSelectedEntryChartBridge.lean
```

New product-side names:

```lean
case2SourceResidualBlockExtension
case2SourceResidualBlock_extension
case2DisplayedPostPivotResidualBlock_sourceResidualBlockExtension
case2DisplayedPostPivotFreeCprimeOfFollowingFactor
case2DisplayedPostPivotFreeFollowingFactor_freeCprimeOfFollowingFactor
Matrix.submatrix_id_equiv_symm_mul_one_submatrix_id_equiv
exists_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_matrix_of_colEquiv
```

New selected-entry names:

```lean
case2SuccessorSelectedEntryMatrix
case2SuccessorSelectedEntryMatrix_ne_zero_of_yNext_pivot_ne_zero
exists_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_successorSelectedEntryMatrix_of_yNext_pivot_ne_zero
exists_residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_eq_successorSelectedEntryMatrix_of_yNext_pivot_ne_zero
```

## Inputs

- `hS : 1 <= S`.
- Old continuation `hcont : J+1 <= prefixMinNat n (S+1)`.
- Successor continuation `hnext : J+2 <= prefixMinNat n (S+1)`.
- A successor selected-entry coordinate vector `yNext`.
- A right-endpoint equivalence
  `eNext : tau ~= Case2ResidualColIndex n S (J+1)`.
- Nonzero successor pivot coordinate `yNext (J+2,J+2) != 0`.

## Proof Basis

The residual block is constructed by zero-extending
`M.submatrix id eNext.symm` to source coordinates at stage `(S,J+1)`.  In the
old displayed normalized block, the old pivot row and column are therefore zero
off the pivot, so `pivotFirstSchurComplement_apply` reduces the post-pivot
Schur block to the prescribed matrix.

The free `Cprime` is constructed with zero top row and lower tail the reindexed
identity following factor.  The displayed product is therefore

```text
M.submatrix id eNext.symm * (1.submatrix id eNext) = M.
```

For `M = case2SuccessorSelectedEntryMatrix ...`, the selected-entry pivot
coordinate is `yNext (J+2,J+2)`, so the product is nonzero.

## Nonclaims

This does not prove displayed-product nonzeroness for an arbitrary
retained-passive source/readback point. It does not prove factor alignment for
`sourceReadback`, retained-passive-to-selected-entry measure transport,
original source-prior transport, normal crossings, pole order, or RLCT.

## Verification

Focused build of
`DLNFibre.DLN.Aoyagi.Case2ResidualSelectedEntryChartBridge`, full `DLNFibre`
build, `scripts/sorries`, `git diff --check`, changed-Lean-file
forbidden-marker search, direct axiom-footprint audit, and xhigh review by
`Wegener` passed.  The new public endpoints report
`[propext, Classical.choice, Quot.sound]`.
