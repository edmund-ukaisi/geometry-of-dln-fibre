import DLNFibre.DLN.RLCT.Validate.RouteM3333

/-!
# `RouteM3333Atom` — the `(3,3,3,3)` chart-Jacobian determinant infrastructure

The determinant rung on top of the banked `RouteM3333` infrastructure (the `Frame3333 ∘ Kparam3333`
decomposition, the two 27-row `HasFDerivAt`, the measure-preserving outer reshape `Q3333CLM`). This
module imports that infra (the heavy `HasFDerivAt` come in as oleans, no re-elaboration) and carries
the determinant building blocks toward `|det Dφ3333| = |u 0|⁵·|u 1|⁴·|u 4|²·|u 9|³`.

## What is PROVED here (sorry-free)

* **`Kparam3333Deriv_det`**: `det (Kparam3333Deriv x) = (x 1)²`. The LDU-core parametrization Jacobian
  is LOWER-triangular in the natural `Fin 27` order (rows `2,3,4` read only lower-indexed columns),
  diagonal `1,1,x1,x1,1,…`, so `det = ∏ diag = (x 1)²` (`Matrix.det_of_lowerTriangular`).
* **`Frame3333Deriv_blockTri`**: `Frame3333Deriv` is `BlockTriangular` over the SCC-condensation grading
  `frameB`. The blocks: five `z 0`-blocks (`[13]`, `[14]`, `[18,21,24]`, `[19,22,25]`, `[20,23,26]`),
  one `z 9³`-block (`[10,11,12]`), one `(z 1·z 4 − z 2·z 3)²`-block (`[0,1,2,5,6,7,8]`, the A-frame
  K/Kᵀ coupling), 6 singletons (det `1`).
* **`K7sub_det`**: `det K7sub = (z 1·z 4 − z 2·z 3)²` — the 7×7 K/Kᵀ coupling-block determinant, in its
  column-reordered (cols `[1,2,5,6,0,3,4]`) block-lower-triangular form `fromBlocks K7tl 0 K7bl K7br`
  (`det = det K7tl · det K7br`, each `= z 1·z 4 − z 2·z 3`). The genuine multi-pivot content.

## What is DEFERRED (the assembly, see thread report)

The numerical ground truth is cert-verified: the exact 27×27 det is `u⁵·a⁴·δ²·b³` (`a = u 1`, `δ = u 4`,
`b = u 9`; `scripts/verify_codex_3333.py`), and `det Frame3333Deriv (Kparam x) · det Kparam3333Deriv x`
gives exactly `x 0⁵·x 1⁴·x 4²·x 9³`, matching `RouteM3333.leafH3333_prod_eq` — NO `leafH3333` adjustment
needed. The remaining work to `routeMCore_box_diverges_achiever_3333`:
(1) `Frame3333Deriv_det` from `BlockTriangular.det` (the `∏ toSquareBlock` product over `frameB`'s image,
    the multi-block `toSquareBlock`s reduced to `K7sub`/the 3×3 `z 0`/`z 9` blocks via `det_reindex`);
(2) `phi3333_abs_det` via `LinearMap.det_comp` + `Q3333CLM_abs_det`;
(3) `phi3333_injOn` (the triangular coordinate-recovery chain, each step a single division or a 2×2
    system of det `x 1·x 4`, off `{u 0=0}∪{u 1=0}∪{u 4=0}∪{u 9=0}`);
(4) `phi3333_cov` (4-axis null-slice add-back, mirroring `RouteMLayerCoverGEL2.phi334_cov`);
(5) `nodeChart3333 : NodeAchieverChart M3333` + the atom (mirroring `RouteM4422`).
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

/-! ## The `Kparam3333Deriv` determinant (lower-triangular, `det = (x 1)²`) -/

set_option maxHeartbeats 1600000 in
/-- **`det Kparam3333Deriv = (x 1)²`.** The Jacobian is lower-triangular in the `Fin 27` order: the
only non-projection rows are `2,3,4`, each reading only columns `≤` its index, so the strictly-upper
entries vanish (`BlockTriangular toDual`); the diagonal product is `1·1·(x 1)·(x 1)·1·…·1 = (x 1)²`. -/
theorem Kparam3333Deriv_det (x : Fin 27 → ℝ) :
    (Kparam3333Deriv x).det = (x 1) ^ 2 := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix']
  set M := LinearMap.toMatrix' (Kparam3333Deriv x : (Fin 27 → ℝ) →ₗ[ℝ] (Fin 27 → ℝ)) with hM
  have htri : M.BlockTriangular OrderDual.toDual := by
    intro i j hij
    rw [OrderDual.toDual_lt_toDual] at hij
    have hijv : (i : ℕ) < (j : ℕ) := hij
    rw [hM, LinearMap.toMatrix'_apply]
    show (Kparam3333Deriv x) (Pi.single j 1) i = 0
    rw [Kparam3333Deriv]
    -- `i < j`: the entry reads column `j > i`, zero for projection + LDU-core rows (cols `≤ i`)
    fin_cases i <;>
      simp only [ContinuousLinearMap.pi_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.cons_val,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul, Pi.single_apply] <;>
      · split_ifs with h1 h2 <;> simp_all <;> omega
  rw [Matrix.det_of_lowerTriangular _ htri]
  -- the diagonal: `M i i = 1` except `M 2 2 = M 3 3 = x 1`
  have hdiag : ∀ i : Fin 27, M i i
      = (if i = 2 then x 1 else if i = 3 then x 1 else 1) := by
    intro i
    rw [hM, LinearMap.toMatrix'_apply]
    show (Kparam3333Deriv x) (Pi.single i 1) i = _
    rw [Kparam3333Deriv]
    fin_cases i <;>
      simp only [ContinuousLinearMap.pi_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.cons_val,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul, Pi.single_apply] <;>
      simp_all <;> norm_num
  rw [Finset.prod_congr rfl (fun i _ => hdiag i)]
  -- evaluate the product over `Fin 27`
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  norm_num [Fin.ext_iff]
  ring

/-! ## The `Frame3333Deriv` block grading + block-triangularity

`Frame3333Deriv` is block-triangular over the SCC-condensation grading `frameB`. The blocks are the five
`z 0`-blocks (`[13]`, `[14]`, `[18,21,24]`, `[19,22,25]`, `[20,23,26]`), the `z 9³`-block `[10,11,12]`,
the `(z 1·z 4 − z 2·z 3)²`-block `[0,1,2,5,6,7,8]` (the A-frame K/Kᵀ coupling), and 6 singletons
(det `1`). The block determinants are banked below; the full `Frame3333Deriv_det` assembles them via
`Matrix.BlockTriangular.det` (deferred — see module note). -/

/-- SCC-condensation block grading for `Frame3333Deriv`: `frameB j < frameB i ⟹ entry (i,j) = 0`. -/
def frameB : Fin 27 → ℕ :=
  ![9, 9, 9, 11, 12, 9, 9, 9, 9, 6, 5, 5, 5, 0, 1, 10, 7, 8, 2, 3, 4, 2, 3, 4, 2, 3, 4]

set_option maxHeartbeats 3200000 in
/-- **`Frame3333Deriv` is block-triangular over `frameB`** (`frameB j < frameB i ⟹ M i j = 0`). The
soundness-critical structural fact: the bilinear-frame Jacobian decomposes into the K/Kᵀ, `z 9`, and
`z 0` blocks; entries jumping to a strictly-lower block vanish. -/
theorem Frame3333Deriv_blockTri (z : Fin 27 → ℝ) :
    (LinearMap.toMatrix' (Frame3333Deriv z :
        (Fin 27 → ℝ) →ₗ[ℝ] (Fin 27 → ℝ))).BlockTriangular frameB := by
  intro i j hij
  rw [LinearMap.toMatrix'_apply]
  show (Frame3333Deriv z) (Pi.single j 1) i = 0
  rw [Frame3333Deriv]
  fin_cases i <;>
    simp only [ContinuousLinearMap.pi_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.cons_val,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, Pi.single_apply] <;>
    · split_ifs <;>
      first
        | rfl
        | (exfalso; subst_vars; revert hij; decide)
        | (simp only [mul_zero, mul_one, add_zero, zero_add])

/-! ## The K/Kᵀ `(z 1·z 4 − z 2·z 3)²` block determinant (the 7×7 coupling block)

The genuine multi-pivot block (`Frame`'s A-frame `[[I];[λ]]·K·[I|m]` coupling). In its
column-reordered (cols `[1,2,5,6,0,3,4]`) block-lower-triangular form `K7sub` it is
`fromBlocks K7tl 0 K7bl K7br` (under `finSumFinEquiv : Fin 4 ⊕ Fin 3 ≃ Fin 7`), with both diagonal
blocks of determinant `z 1·z 4 − z 2·z 3`, so the 7×7 block determinant is `(z 1·z 4 − z 2·z 3)²`. -/

/-- The 7×7 K-coupling block in COLUMN-REORDERED block-lower-triangular form (cols `[1,2,5,6,0,3,4]`). -/
noncomputable def K7sub (z : Fin 27 → ℝ) : Matrix (Fin 7) (Fin 7) ℝ :=
  !![1, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0;
     z 7, z 8, z 1, z 2, 0, 0, 0;
     0, 0, z 3, z 4, 0, 0, 0;
     z 5, 0, 0, 0, 0, z 1, z 3;
     0, z 5, 0, 0, 0, z 2, z 4;
     z 5 * z 7, z 5 * z 8, z 1 * z 5 + z 3 * z 6, z 2 * z 5 + z 4 * z 6, 1,
       z 1 * z 7 + z 2 * z 8, z 3 * z 7 + z 4 * z 8]

/-- Top-left 4×4 block of `K7sub` (block-lower-tri itself: `det = z 1·z 4 − z 2·z 3`). -/
noncomputable def K7tl (z : Fin 27 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; z 7, z 8, z 1, z 2; 0, 0, z 3, z 4]

/-- Bottom-right 3×3 block of `K7sub` (`det = z 1·z 4 − z 2·z 3`). -/
noncomputable def K7br (z : Fin 27 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, z 1, z 3; 0, z 2, z 4; 1, z 1 * z 7 + z 2 * z 8, z 3 * z 7 + z 4 * z 8]

/-- Bottom-left 3×4 block of `K7sub`. -/
noncomputable def K7bl (z : Fin 27 → ℝ) : Matrix (Fin 3) (Fin 4) ℝ :=
  !![z 5, 0, 0, 0; 0, z 5, 0, 0; z 5 * z 7, z 5 * z 8, z 1 * z 5 + z 3 * z 6, z 2 * z 5 + z 4 * z 6]

/-- `K7tl` reindexed by `finSumFinEquiv` (split `Fin 2 ⊕ Fin 2`) is `fromBlocks I₂ 0 C [[z1,z2],[z3,z4]]`. -/
theorem K7tl_submatrix_eq (z : Fin 27 → ℝ) :
    (K7tl z).submatrix finSumFinEquiv finSumFinEquiv
      = Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) ℝ) 0
          (!![z 7, z 8; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)
          (!![z 1, z 2; z 3, z 4] : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, K7tl, Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.cons_val,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.one_apply_eq, Matrix.one_apply_ne,
      Fin.castAdd_zero, Matrix.of_apply] <;> rfl

/-- **`det K7tl = z 1·z 4 − z 2·z 3`** (block-lower-tri `[[I₂,0],[C,K]]`, `det = 1·det K`). -/
theorem K7tl_det (z : Fin 27 → ℝ) : (K7tl z).det = z 1 * z 4 - z 2 * z 3 := by
  have h := Matrix.det_submatrix_equiv_self (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4) (K7tl z)
  rw [K7tl_submatrix_eq] at h
  rw [← h, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, Matrix.det_fin_two_of, one_mul]

/-- **`det K7br = z 1·z 4 − z 2·z 3`** (3×3 cofactor along the bottom `1`). -/
theorem K7br_det (z : Fin 27 → ℝ) : (K7br z).det = z 1 * z 4 - z 2 * z 3 := by
  rw [K7br, Matrix.det_fin_three]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_fin_const]
  ring

set_option maxHeartbeats 1200000 in
/-- `K7sub` reindexed by `finSumFinEquiv` (split `Fin 4 ⊕ Fin 3`) is `fromBlocks K7tl 0 K7bl K7br`. -/
theorem K7sub_submatrix_eq (z : Fin 27 → ℝ) :
    (K7sub z).submatrix finSumFinEquiv finSumFinEquiv
      = Matrix.fromBlocks (K7tl z) 0 (K7bl z) (K7br z) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, K7sub, K7tl, K7br, K7bl, Fin.isValue, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const,
      Matrix.cons_val, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply] <;> rfl

set_option maxHeartbeats 800000 in
/-- **`det K7sub = (z 1·z 4 − z 2·z 3)²`** — the 7×7 K/Kᵀ coupling-block determinant, via the
`fromBlocks K7tl 0 K7bl K7br` decomposition (`det = det K7tl · det K7br`). -/
theorem K7sub_det (z : Fin 27 → ℝ) : (K7sub z).det = (z 1 * z 4 - z 2 * z 3) ^ 2 := by
  have h := Matrix.det_submatrix_equiv_self (finSumFinEquiv : Fin 4 ⊕ Fin 3 ≃ Fin 7) (K7sub z)
  rw [K7sub_submatrix_eq] at h
  rw [← h, Matrix.det_fromBlocks_zero₁₂, K7tl_det, K7br_det]
  ring

end DLNFibre.DLN.RLCT
