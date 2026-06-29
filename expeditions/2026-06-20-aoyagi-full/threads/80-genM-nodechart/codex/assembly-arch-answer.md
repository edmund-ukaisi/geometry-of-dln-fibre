**Verdict:** choose **Route A, det-level**, not `composeFold` map equality and not global `twoStairConj`.

The least-cast spine is:

1. Work with `J := LinearMap.toMatrix' (fderiv ℝ phiFlatLiveR1 u).toLinearMap`.
2. Prove a column-factor statement
   `J = Matrix.of fun i j => (if j ∈ Rcols then u_p else 1) * G i j`,
   with `Rcols.card = minAdm M - 1`.
3. Use a local matrix lemma to get
   `|J.det| = |u_p|^(minAdm M - 1) * |G.det|`.
4. Prove `G` is block-lower-triangular by the existing grading/locality machinery, and identify each diagonal boundary block with the native Schur/LDU engine.

This avoids both the recursive `StairProd` target and a global `composeFold fs = phiFlatLiveR1` map equality.

For Q1: yes. In mathlib v4.29 there are single-column lemmas `Matrix.det_updateCol_smul`, but for a finite set of columns the cleaner lemma is diagonal/column scaling. Use `Matrix.det_mul`, `Matrix.det_diagonal`, or the wrapper around `Matrix.det_mul_row` whose statement scales by the column index:
```lean
Matrix.det (Matrix.of fun i j => v j * A i j) = (∏ j, v j) * A.det
```
Then set `v j := if j ∈ Rcols then u_p else 1`. Do not divide by `u_p`; this stays valid at `u_p = 0`.

For Q2: Route B is almost certainly more cast-heavy. The banked wrapper [RouteMStairTwoSidedHeadline.lean](</home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4/lean/DLNFibre/DLN/RLCT/Validate/RouteMStairTwoSidedHeadline.lean:40>) is good, but the remaining proof is a full linear-map equality
`eOut ∘ Dφ ∘ eIn.symm = stairMap`. That forces exact agreement of every recursive tail, coupling, input regrouping, output regrouping, and shear. The det-level route only asks for column scaling, block triangularity, and diagonal block determinants.

For Q3: use **per-boundary local equivalences**, not a global `StairProd`. For each `s`, build row/column reindex/CLEs from the `toSquareBlock` subtype to the native engine coordinates, then prove:
```lean
|(G.toSquareBlock grade (s.val + 1)).det|
  = |Kdet s| ^ (r_s + c_s)
    * ∏ i : Fin (t_s), |q_s i| ^ (2 * (t_s - 1 - i))
```
The determinant proof should use `Matrix.abs_det_reindex`, `LinearMap.det_comp`, `schurFrame_abs_det`, and `lduCoreDeriv_abs_det`. The value bridge uses the banked `schurFrameProd_block_K/_KN/_XK/_XKNuE`; the determinant engine itself is already native in [RouteMSchurFrameDet.lean](</home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4/lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurFrameDet.lean:287>) and packaged in [RouteMFactorMaps.lean](</home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4/lean/DLNFibre/DLN/RLCT/Validate/RouteMFactorMaps.lean:185>).

For Q4: delegate only after fixing the shared API. Do **not** parallelize the global `V/eIn/eOut/stairMap` construction; those choices are too coupled. For Route A, parallelism is clean once you freeze names/signatures for `Rcols`, `grade`, `G`, and the per-boundary block equivalences.

**First two bankable lemmas:**

1. `Matrix.abs_det_scaledColumns_finset`
```lean
| (Matrix.of fun i j => (if j ∈ S then u else 1) * G i j).det |
  = |u| ^ S.card * |G.det|
```

2. `interior_abs_det_of_columnFactorization`
```lean
J = scaledColumns Rcols u_p G →
Rcols.card = minAdm M - 1 →
|G.det| = ∏ s, engine s →
|LinearMap.det D| = |u_p|^(minAdm M - 1) * ∏ s, engine s
```

Then build the hard content behind the hypotheses: `phiFlatLiveR1_jacobian_scaledColumns` and `boundary_diagBlock_abs_det_engine`. No code changes made; I only inspected the local v4.29/mathlib and repo APIs.