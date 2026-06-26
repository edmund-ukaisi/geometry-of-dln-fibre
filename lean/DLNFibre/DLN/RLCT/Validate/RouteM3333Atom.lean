import DLNFibre.DLN.RLCT.Validate.RouteM3333

/-!
# `RouteM3333Atom` — the `(3,3,3,3)` achiever box-divergence (the decisive multi-pivot node)

The determinant + change-of-variables + achiever box-divergence atom on top of the banked `RouteM3333`
infrastructure (the `Frame3333 ∘ Kparam3333` decomposition, the two 27-row `HasFDerivAt`, the
measure-preserving outer reshape `Q3333CLM`). This module imports that infra (the heavy `HasFDerivAt`
come in as oleans, no re-elaboration) and carries the determinant + c-o-v + the atom
`routeMCore_box_diverges_achiever_3333` (the `(3,3,3,3)` instance, NOT the general-`M` atom).

## The chart Jacobian `|det Dφ3333| = |u 0|⁵·|u 1|⁴·|u 4|²·|u 9|³` (`phi3333_abs_det`)

The exact 27×27 det is `u⁵·a⁴·δ²·b³` (`a = u 1`, `δ = u 4`, `b = u 9`; cert-verified
`scripts/verify_codex_3333.py`), via `LinearMap.det_comp` on `T3333 = Frame3333 ∘ Kparam3333` + the
measure-preserving outer reshape `|det Q3333| = 1`. It MATCHES `RouteM3333.leafH3333_prod_eq`'s RHS
exactly — NO `leafH3333` adjustment needed.

* `Kparam3333Deriv_det`: `det = (x 1)²` — the LDU-core parametrization Jacobian is LOWER-triangular
  (diagonal `1,1,x1,x1,1,…`).
* `Frame3333Deriv_det`: `det = (z 0)⁵·(z 9)³·(z 1·z 4 − z 2·z 3)²`, assembled from the
  `BlockTriangular.det` over the SCC grading `frameB` (image `{0,…,12}`): five `z 0`-blocks
  (`[13]`,`[14]`,`[18,21,24]`,`[19,22,25]`,`[20,23,26]`), the `z 9³`-block `[10,11,12]`, the
  `(z 1·z 4 − z 2·z 3)²`-block `[0,1,2,5,6,7,8]` (the A-frame K/Kᵀ coupling, via the column-reorder
  to block-lower-triangular form `fromBlocks K7tl 0 K7bl K7br`), the rest singletons (det `1`).
* Composing (`Kparam3333` sends `z 1·z 4 − z 2·z 3 = u 1·u 4`): `1·(u0⁵·u9³·(u1·u4)²)·u1² =
  u0⁵·u1⁴·u4²·u9³`.

## The atom (`routeMCore_box_diverges_achiever_3333`, axiom profile = the `(4,4,2,2)` sibling)

`nodeChart3333 : NodeAchieverChart M3333` bundles `phi3333` (binding axis `0`), the genuine c-o-v
`phi3333_cov` (off `{u 0=0}∪{u 1=0}∪{u 4=0}∪{u 9=0}`, where `phi3333_injOn` — the triangular coord
recovery, each step a division by `u 1`/`u 9`/`u 0` or a `2×2` A-frame system of det `u 1·u 4` —
holds; the three extra slices added back as a null contribution), the unit `Vval3333`, and the banked
`leaf_integrand3333`/`phi3333_image_subset_cubeBox`. Fed through the M-agnostic assembly
`routeMCore_box_diverges_of_nodeChart`. The determinant/c-o-v/injectivity lemmas are axiom-clean
`[propext, Classical.choice, Quot.sound]`; the atom additionally cites the S2 divergence leaf
`monomial_rlct` (via `monomialIntegrand_lintegral_box_eq_top`), exactly as the `(4,4,2,2)` and
`(3,3,4)` instances do.
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

/-- The 7×7 K-coupling block in NATURAL (sub-block) order — rows/cols `0,1,2,5,6,7,8` of the Frame
Jacobian, exactly what `toSquareBlock frameB 9` reindexes to. -/
noncomputable def K7nat (z : Fin 27 → ℝ) : Matrix (Fin 7) (Fin 7) ℝ :=
  !![0, 1, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0;
     0, z 7, z 8, 0, 0, z 1, z 2;
     0, 0, 0, 0, 0, z 3, z 4;
     0, z 5, 0, z 1, z 3, 0, 0;
     0, 0, z 5, z 2, z 4, 0, 0;
     1, z 5 * z 7, z 5 * z 8, z 1 * z 7 + z 2 * z 8, z 3 * z 7 + z 4 * z 8,
       z 1 * z 5 + z 3 * z 6, z 2 * z 5 + z 4 * z 6]

/-- The even column permutation `[1,2,5,6,0,3,4]` taking `K7nat` to its block-lower-triangular `K7sub`. -/
def k7p : Equiv.Perm (Fin 7) where
  toFun := ![1, 2, 5, 6, 0, 3, 4]
  invFun := ![4, 0, 1, 5, 6, 2, 3]
  left_inv := by decide
  right_inv := by decide

set_option maxHeartbeats 1600000 in
/-- `K7sub = K7nat` with columns permuted by `k7p` (per-cell `rfl`). -/
theorem K7sub_eq_perm (z : Fin 27 → ℝ) : K7sub z = (K7nat z).submatrix id k7p := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- **`det K7nat = (z 1·z 4 − z 2·z 3)²`** — the natural-order 7×7 coupling-block determinant. `K7sub`
is `K7nat` column-permuted by the EVEN `k7p` (`sign = 1`), so `det K7nat = det K7sub` (`det_permute'`). -/
theorem K7nat_det (z : Fin 27 → ℝ) : (K7nat z).det = (z 1 * z 4 - z 2 * z 3) ^ 2 := by
  have h : (K7sub z).det = Equiv.Perm.sign k7p * (K7nat z).det := by
    rw [K7sub_eq_perm, Matrix.det_permute']
  rw [K7sub_det, show Equiv.Perm.sign k7p = 1 from by decide] at h
  simpa using h.symm

/-! ## `Frame3333Deriv_det` — assembling the block determinants via `BlockTriangular.det`

`BlockTriangular.det` gives `det = ∏ a ∈ image frameB, (toSquareBlock frameB a).det`. The image is
`{0,…,12}`; the per-value block determinants are read off the Frame Jacobian: the singletons `0,1`
give `z 0`, `6,7,8,10,11,12` give `1`; the 3-blocks `2,3,4` give `z 0`, `5` gives `z 9³`; the 7-block
`9` gives `(z 1·z 4 − z 2·z 3)²` (reindexed to `K7nat`). The product is `z 0⁵·z 9³·(z 1·z 4 − z 2·z 3)²`. -/

/-- The Frame-Jacobian standard-basis matrix. -/
noncomputable abbrev FrameM (z : Fin 27 → ℝ) : Matrix (Fin 27) (Fin 27) ℝ :=
  LinearMap.toMatrix' (Frame3333Deriv z : (Fin 27 → ℝ) →ₗ[ℝ] (Fin 27 → ℝ))

/-- A single `FrameM` entry, read through `Pi.single`. -/
theorem FrameM_entry (z : Fin 27 → ℝ) (i j : Fin 27) :
    FrameM z i j = (Frame3333Deriv z) (Pi.single j 1) i := by
  rw [FrameM, LinearMap.toMatrix'_apply]; rfl

/-- Reduce a single Frame-Jacobian entry to its monomial value. -/
local macro "fm_entry" : tactic =>
  `(tactic| (rw [FrameM_entry, Frame3333Deriv]
             simp only [ContinuousLinearMap.pi_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
               Matrix.head_cons, Matrix.head_fin_const, Matrix.cons_val, ContinuousLinearMap.add_apply,
               ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
               Pi.single_apply, Fin.reduceEq, if_false, if_true, mul_zero, mul_one, add_zero,
               zero_add, neg_zero]))

-- The five multi-block reindex equivs (match-based toFun → clean `rfl` entry extraction).
/-- `Fin 3 ≃ {a // frameB a = 2}` (block `[18,21,24]`). -/
def e2 : Fin 3 ≃ { a : Fin 27 // frameB a = 2 } where
  toFun := fun k => match k with
    | 0 => ⟨18, by decide⟩ | 1 => ⟨21, by decide⟩ | 2 => ⟨24, by decide⟩
  invFun := fun a => if a.1 = 18 then 0 else if a.1 = 21 then 1 else 2
  left_inv := by decide
  right_inv := by decide

/-- `Fin 3 ≃ {a // frameB a = 3}` (block `[19,22,25]`). -/
def e3 : Fin 3 ≃ { a : Fin 27 // frameB a = 3 } where
  toFun := fun k => match k with
    | 0 => ⟨19, by decide⟩ | 1 => ⟨22, by decide⟩ | 2 => ⟨25, by decide⟩
  invFun := fun a => if a.1 = 19 then 0 else if a.1 = 22 then 1 else 2
  left_inv := by decide
  right_inv := by decide

/-- `Fin 3 ≃ {a // frameB a = 4}` (block `[20,23,26]`). -/
def e4 : Fin 3 ≃ { a : Fin 27 // frameB a = 4 } where
  toFun := fun k => match k with
    | 0 => ⟨20, by decide⟩ | 1 => ⟨23, by decide⟩ | 2 => ⟨26, by decide⟩
  invFun := fun a => if a.1 = 20 then 0 else if a.1 = 23 then 1 else 2
  left_inv := by decide
  right_inv := by decide

/-- `Fin 3 ≃ {a // frameB a = 5}` (block `[10,11,12]`). -/
def e5 : Fin 3 ≃ { a : Fin 27 // frameB a = 5 } where
  toFun := fun k => match k with
    | 0 => ⟨10, by decide⟩ | 1 => ⟨11, by decide⟩ | 2 => ⟨12, by decide⟩
  invFun := fun a => if a.1 = 10 then 0 else if a.1 = 11 then 1 else 2
  left_inv := by decide
  right_inv := by decide

/-- `Fin 7 ≃ {a // frameB a = 9}` (block `[0,1,2,5,6,7,8]`, the K/Kᵀ coupling). -/
def e9 : Fin 7 ≃ { a : Fin 27 // frameB a = 9 } where
  toFun := fun k => match k with
    | 0 => ⟨0, by decide⟩ | 1 => ⟨1, by decide⟩ | 2 => ⟨2, by decide⟩ | 3 => ⟨5, by decide⟩
    | 4 => ⟨6, by decide⟩ | 5 => ⟨7, by decide⟩ | 6 => ⟨8, by decide⟩
  invFun := fun a => if a.1 = 0 then 0 else if a.1 = 1 then 1 else if a.1 = 2 then 2
    else if a.1 = 5 then 3 else if a.1 = 6 then 4 else if a.1 = 7 then 5 else 6
  left_inv := by decide
  right_inv := by decide

set_option maxHeartbeats 800000 in
/-- The `z 0`-block determinant `det (toSquareBlock frameB 2) = z 0` (block `[18,21,24]`). -/
theorem toSquareBlock_2_det (z : Fin 27 → ℝ) :
    ((FrameM z).toSquareBlock frameB 2).det = z 0 := by
  rw [← Matrix.det_submatrix_equiv_self e2 ((FrameM z).toSquareBlock frameB 2), Matrix.det_fin_three]
  rw [show (((FrameM z).toSquareBlock frameB 2).submatrix e2 e2) 0 0 = FrameM z 18 18 from rfl,
      show (((FrameM z).toSquareBlock frameB 2).submatrix e2 e2) 0 1 = FrameM z 18 21 from rfl,
      show (((FrameM z).toSquareBlock frameB 2).submatrix e2 e2) 0 2 = FrameM z 18 24 from rfl,
      show (((FrameM z).toSquareBlock frameB 2).submatrix e2 e2) 1 0 = FrameM z 21 18 from rfl,
      show (((FrameM z).toSquareBlock frameB 2).submatrix e2 e2) 1 1 = FrameM z 21 21 from rfl,
      show (((FrameM z).toSquareBlock frameB 2).submatrix e2 e2) 1 2 = FrameM z 21 24 from rfl,
      show (((FrameM z).toSquareBlock frameB 2).submatrix e2 e2) 2 0 = FrameM z 24 18 from rfl,
      show (((FrameM z).toSquareBlock frameB 2).submatrix e2 e2) 2 1 = FrameM z 24 21 from rfl,
      show (((FrameM z).toSquareBlock frameB 2).submatrix e2 e2) 2 2 = FrameM z 24 24 from rfl]
  rw [show FrameM z 18 18 = -z 11 from by fm_entry, show FrameM z 18 21 = -z 12 from by fm_entry,
      show FrameM z 18 24 = z 0 from by fm_entry, show FrameM z 21 18 = 1 from by fm_entry,
      show FrameM z 21 21 = 0 from by fm_entry, show FrameM z 21 24 = 0 from by fm_entry,
      show FrameM z 24 18 = 0 from by fm_entry, show FrameM z 24 21 = 1 from by fm_entry,
      show FrameM z 24 24 = 0 from by fm_entry]
  ring

set_option maxHeartbeats 800000 in
/-- The `z 0`-block determinant `det (toSquareBlock frameB 3) = z 0` (block `[19,22,25]`). -/
theorem toSquareBlock_3_det (z : Fin 27 → ℝ) :
    ((FrameM z).toSquareBlock frameB 3).det = z 0 := by
  rw [← Matrix.det_submatrix_equiv_self e3 ((FrameM z).toSquareBlock frameB 3), Matrix.det_fin_three]
  rw [show (((FrameM z).toSquareBlock frameB 3).submatrix e3 e3) 0 0 = FrameM z 19 19 from rfl,
      show (((FrameM z).toSquareBlock frameB 3).submatrix e3 e3) 0 1 = FrameM z 19 22 from rfl,
      show (((FrameM z).toSquareBlock frameB 3).submatrix e3 e3) 0 2 = FrameM z 19 25 from rfl,
      show (((FrameM z).toSquareBlock frameB 3).submatrix e3 e3) 1 0 = FrameM z 22 19 from rfl,
      show (((FrameM z).toSquareBlock frameB 3).submatrix e3 e3) 1 1 = FrameM z 22 22 from rfl,
      show (((FrameM z).toSquareBlock frameB 3).submatrix e3 e3) 1 2 = FrameM z 22 25 from rfl,
      show (((FrameM z).toSquareBlock frameB 3).submatrix e3 e3) 2 0 = FrameM z 25 19 from rfl,
      show (((FrameM z).toSquareBlock frameB 3).submatrix e3 e3) 2 1 = FrameM z 25 22 from rfl,
      show (((FrameM z).toSquareBlock frameB 3).submatrix e3 e3) 2 2 = FrameM z 25 25 from rfl]
  rw [show FrameM z 19 19 = -z 11 from by fm_entry, show FrameM z 19 22 = -z 12 from by fm_entry,
      show FrameM z 19 25 = z 0 from by fm_entry, show FrameM z 22 19 = 1 from by fm_entry,
      show FrameM z 22 22 = 0 from by fm_entry, show FrameM z 22 25 = 0 from by fm_entry,
      show FrameM z 25 19 = 0 from by fm_entry, show FrameM z 25 22 = 1 from by fm_entry,
      show FrameM z 25 25 = 0 from by fm_entry]
  ring

set_option maxHeartbeats 800000 in
/-- The `z 0`-block determinant `det (toSquareBlock frameB 4) = z 0` (block `[20,23,26]`). -/
theorem toSquareBlock_4_det (z : Fin 27 → ℝ) :
    ((FrameM z).toSquareBlock frameB 4).det = z 0 := by
  rw [← Matrix.det_submatrix_equiv_self e4 ((FrameM z).toSquareBlock frameB 4), Matrix.det_fin_three]
  rw [show (((FrameM z).toSquareBlock frameB 4).submatrix e4 e4) 0 0 = FrameM z 20 20 from rfl,
      show (((FrameM z).toSquareBlock frameB 4).submatrix e4 e4) 0 1 = FrameM z 20 23 from rfl,
      show (((FrameM z).toSquareBlock frameB 4).submatrix e4 e4) 0 2 = FrameM z 20 26 from rfl,
      show (((FrameM z).toSquareBlock frameB 4).submatrix e4 e4) 1 0 = FrameM z 23 20 from rfl,
      show (((FrameM z).toSquareBlock frameB 4).submatrix e4 e4) 1 1 = FrameM z 23 23 from rfl,
      show (((FrameM z).toSquareBlock frameB 4).submatrix e4 e4) 1 2 = FrameM z 23 26 from rfl,
      show (((FrameM z).toSquareBlock frameB 4).submatrix e4 e4) 2 0 = FrameM z 26 20 from rfl,
      show (((FrameM z).toSquareBlock frameB 4).submatrix e4 e4) 2 1 = FrameM z 26 23 from rfl,
      show (((FrameM z).toSquareBlock frameB 4).submatrix e4 e4) 2 2 = FrameM z 26 26 from rfl]
  rw [show FrameM z 20 20 = -z 11 from by fm_entry, show FrameM z 20 23 = -z 12 from by fm_entry,
      show FrameM z 20 26 = z 0 from by fm_entry, show FrameM z 23 20 = 1 from by fm_entry,
      show FrameM z 23 23 = 0 from by fm_entry, show FrameM z 23 26 = 0 from by fm_entry,
      show FrameM z 26 20 = 0 from by fm_entry, show FrameM z 26 23 = 1 from by fm_entry,
      show FrameM z 26 26 = 0 from by fm_entry]
  ring

set_option maxHeartbeats 800000 in
/-- The `z 9³`-block determinant `det (toSquareBlock frameB 5) = z 9³` (block `[10,11,12]`). -/
theorem toSquareBlock_5_det (z : Fin 27 → ℝ) :
    ((FrameM z).toSquareBlock frameB 5).det = (z 9) ^ 3 := by
  rw [← Matrix.det_submatrix_equiv_self e5 ((FrameM z).toSquareBlock frameB 5), Matrix.det_fin_three]
  rw [show (((FrameM z).toSquareBlock frameB 5).submatrix e5 e5) 0 0 = FrameM z 10 10 from rfl,
      show (((FrameM z).toSquareBlock frameB 5).submatrix e5 e5) 0 1 = FrameM z 10 11 from rfl,
      show (((FrameM z).toSquareBlock frameB 5).submatrix e5 e5) 0 2 = FrameM z 10 12 from rfl,
      show (((FrameM z).toSquareBlock frameB 5).submatrix e5 e5) 1 0 = FrameM z 11 10 from rfl,
      show (((FrameM z).toSquareBlock frameB 5).submatrix e5 e5) 1 1 = FrameM z 11 11 from rfl,
      show (((FrameM z).toSquareBlock frameB 5).submatrix e5 e5) 1 2 = FrameM z 11 12 from rfl,
      show (((FrameM z).toSquareBlock frameB 5).submatrix e5 e5) 2 0 = FrameM z 12 10 from rfl,
      show (((FrameM z).toSquareBlock frameB 5).submatrix e5 e5) 2 1 = FrameM z 12 11 from rfl,
      show (((FrameM z).toSquareBlock frameB 5).submatrix e5 e5) 2 2 = FrameM z 12 12 from rfl]
  rw [show FrameM z 10 10 = 0 from by fm_entry, show FrameM z 10 11 = z 9 from by fm_entry,
      show FrameM z 10 12 = 0 from by fm_entry, show FrameM z 11 10 = 0 from by fm_entry,
      show FrameM z 11 11 = 0 from by fm_entry, show FrameM z 11 12 = z 9 from by fm_entry,
      show FrameM z 12 10 = z 9 from by fm_entry, show FrameM z 12 11 = 0 from by fm_entry,
      show FrameM z 12 12 = 0 from by fm_entry]
  ring

set_option maxHeartbeats 1600000 in
/-- The 7×7 K/Kᵀ-coupling block determinant `det (toSquareBlock frameB 9) = (z 1·z 4 − z 2·z 3)²`. -/
theorem toSquareBlock_9_det (z : Fin 27 → ℝ) :
    ((FrameM z).toSquareBlock frameB 9).det = (z 1 * z 4 - z 2 * z 3) ^ 2 := by
  rw [← Matrix.det_submatrix_equiv_self e9 ((FrameM z).toSquareBlock frameB 9), ← K7nat_det z]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp only [Matrix.submatrix_apply, Matrix.toSquareBlock_def, Matrix.of_apply, e9,
        Equiv.coe_fn_mk, K7nat, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons, Matrix.head_cons,
        Matrix.head_fin_const, Matrix.cons_val, Matrix.cons_val', Matrix.cons_val_fin_one,
        Fin.isValue]
      first | rfl | (fm_entry; rfl) | fm_entry

/-- Singleton `toSquareBlock` determinant: `det = the diagonal entry at the block's single index `p``. -/
local macro "singleton_det" k:term ", " p:term : tactic =>
  `(tactic| (haveI : Subsingleton { a : Fin 27 // frameB a = $k } := by
               constructor; rintro ⟨a, ha⟩ ⟨b, hb⟩; apply Subtype.ext; revert ha hb; revert a b; decide
             rw [Matrix.det_eq_elem_of_subsingleton _ ⟨$p, by decide⟩, Matrix.toSquareBlock_def,
               Matrix.of_apply]
             fm_entry))

set_option maxHeartbeats 800000 in
theorem toSquareBlock_0_det (z : Fin 27 → ℝ) : ((FrameM z).toSquareBlock frameB 0).det = z 0 := by
  singleton_det 0, 13
set_option maxHeartbeats 800000 in
theorem toSquareBlock_1_det (z : Fin 27 → ℝ) : ((FrameM z).toSquareBlock frameB 1).det = z 0 := by
  singleton_det 1, 14
set_option maxHeartbeats 800000 in
theorem toSquareBlock_6_det (z : Fin 27 → ℝ) : ((FrameM z).toSquareBlock frameB 6).det = 1 := by
  singleton_det 6, 9
set_option maxHeartbeats 800000 in
theorem toSquareBlock_7_det (z : Fin 27 → ℝ) : ((FrameM z).toSquareBlock frameB 7).det = 1 := by
  singleton_det 7, 16
set_option maxHeartbeats 800000 in
theorem toSquareBlock_8_det (z : Fin 27 → ℝ) : ((FrameM z).toSquareBlock frameB 8).det = 1 := by
  singleton_det 8, 17
set_option maxHeartbeats 800000 in
theorem toSquareBlock_10_det (z : Fin 27 → ℝ) : ((FrameM z).toSquareBlock frameB 10).det = 1 := by
  singleton_det 10, 15
set_option maxHeartbeats 800000 in
theorem toSquareBlock_11_det (z : Fin 27 → ℝ) : ((FrameM z).toSquareBlock frameB 11).det = 1 := by
  singleton_det 11, 3
set_option maxHeartbeats 800000 in
theorem toSquareBlock_12_det (z : Fin 27 → ℝ) : ((FrameM z).toSquareBlock frameB 12).det = 1 := by
  singleton_det 12, 4

set_option maxHeartbeats 1600000 in
/-- **`det Frame3333Deriv = (z 0)⁵·(z 9)³·(z 1·z 4 − z 2·z 3)²`** — assembled from the block
determinants via `Matrix.BlockTriangular.det` over `image frameB = {0,…,12}`. -/
theorem Frame3333Deriv_det (z : Fin 27 → ℝ) :
    (Frame3333Deriv z).det = (z 0) ^ 5 * (z 9) ^ 3 * (z 1 * z 4 - z 2 * z 3) ^ 2 := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix']
  rw [show LinearMap.toMatrix' (Frame3333Deriv z : (Fin 27 → ℝ) →ₗ[ℝ] (Fin 27 → ℝ)) = FrameM z from rfl]
  rw [(Frame3333Deriv_blockTri z).det,
    show Finset.image frameB Finset.univ
      = ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} : Finset ℕ) from by decide]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  rw [toSquareBlock_0_det, toSquareBlock_1_det, toSquareBlock_2_det, toSquareBlock_3_det,
    toSquareBlock_4_det, toSquareBlock_5_det, toSquareBlock_6_det, toSquareBlock_7_det,
    toSquareBlock_8_det, toSquareBlock_9_det, toSquareBlock_10_det, toSquareBlock_11_det,
    toSquareBlock_12_det]
  ring

/-! ## The chart Jacobian `|det Dφ3333| = |u 0|⁵·|u 1|⁴·|u 4|²·|u 9|³`

`phi3333 = Q3333 ∘ T3333` with `T3333 = Frame3333 ∘ Kparam3333` (banked). The chain rule + fderiv
uniqueness give `T3333Deriv = Frame3333Deriv(Kparam x) ∘ Kparam3333Deriv x`, so by `det_comp` the
chart Jacobian det is `|det Q3333|·|det Frame3333Deriv(Kparam x)|·|det Kparam3333Deriv x| =
1·(u0⁵·u9³·(u1·u4)²)·(u1²)` (substituting the `Kparam3333` coords, `z 1·z 4 − z 2·z 3 = u 1·u 4`),
matching `leafH3333_prod_eq`'s RHS. -/

/-- `phi3333 = Q3333CLM ∘ T3333` (`= paramsEquivFlat ∘ pack3333 ∘ T3333`). -/
theorem phi3333_eq_Q_T (x : Fin 27 → ℝ) : phi3333 x = Q3333CLM (T3333 x) := by
  rw [phi3333, chartParams3333_eq_pack_T]
  have : Q3333CLM (T3333 x) = paramsEquivFlatCLE M3333 (pack3333CLM (T3333 x)) := rfl
  rw [this, paramsEquivFlatCLE_coe, pack3333CLM_coe]

/-- `T3333Deriv = Frame3333Deriv(Kparam x) ∘ Kparam3333Deriv x` (chain rule + fderiv uniqueness). -/
theorem T3333Deriv_eq_comp (x : Fin 27 → ℝ) :
    T3333Deriv x = (Frame3333Deriv (Kparam3333 x)).comp (Kparam3333Deriv x) := by
  have h1 : HasFDerivAt T3333 (T3333Deriv x) x := T3333_hasFDerivAt x
  have h2 : HasFDerivAt T3333 ((Frame3333Deriv (Kparam3333 x)).comp (Kparam3333Deriv x)) x := by
    have hcomp := (Frame3333_hasFDerivAt (Kparam3333 x)).comp x (Kparam3333_hasFDerivAt x)
    have he : (Frame3333 ∘ Kparam3333) = T3333 := by funext y; exact Frame3333_Kparam3333 y
    rwa [he] at hcomp
  exact h1.unique h2

/-- The genuine chart fderiv `phi3333Deriv u = Q3333CLM ∘ T3333Deriv u`. -/
noncomputable def phi3333Deriv (u : Fin 27 → ℝ) : (Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ) :=
  Q3333CLM.comp (T3333Deriv u)

/-- **`phi3333` has fderiv `phi3333Deriv`** (chain rule for `phi3333 = Q3333 ∘ T3333`). -/
theorem phi3333_hasFDerivAt (u : Fin 27 → ℝ) : HasFDerivAt phi3333 (phi3333Deriv u) u := by
  have hT : HasFDerivAt T3333 (T3333Deriv u) u := T3333_hasFDerivAt u
  have hQ : HasFDerivAt (Q3333CLM : (Fin 27 → ℝ) → (Fin 27 → ℝ)) Q3333CLM (T3333 u) :=
    Q3333CLM.hasFDerivAt
  have hc := hQ.comp u hT
  have he : (Q3333CLM : (Fin 27 → ℝ) → (Fin 27 → ℝ)) ∘ T3333 = phi3333 := by
    funext x; rw [Function.comp_apply, ← phi3333_eq_Q_T]
  rwa [he] at hc

/-- `phi3333` is differentiable. -/
theorem differentiable_phi3333 : Differentiable ℝ phi3333 :=
  fun u => (phi3333_hasFDerivAt u).differentiableAt

/-- The `Kparam3333` coordinate values used in the det composition. -/
theorem Kparam3333_eval (u : Fin 27 → ℝ) :
    Kparam3333 u 0 = u 0 ∧ Kparam3333 u 1 = u 1 ∧ Kparam3333 u 2 = u 1 * u 2
      ∧ Kparam3333 u 3 = u 1 * u 3 ∧ Kparam3333 u 4 = u 1 * u 2 * u 3 + u 4
      ∧ Kparam3333 u 9 = u 9 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The genuine chart Jacobian determinant** `|det Dφ3333| = |u 0|⁵·|u 1|⁴·|u 4|²·|u 9|³` — via
`det_comp` on `phi3333Deriv = Q3333CLM ∘ (Frame3333Deriv(Kparam u) ∘ Kparam3333Deriv u)`:
`1·(u0⁵·u9³·(u1·u4)²)·u1²`. Matches `RouteM3333.leafH3333_prod_eq`'s RHS. -/
theorem phi3333_abs_det (u : Fin 27 → ℝ) :
    |(phi3333Deriv u).det| = |u 0| ^ 5 * |u 1| ^ 4 * |u 4| ^ 2 * |u 9| ^ 3 := by
  rw [phi3333Deriv, ContinuousLinearMap.det, ContinuousLinearMap.coe_comp, LinearMap.det_comp,
    ← ContinuousLinearMap.det, ← ContinuousLinearMap.det, abs_mul, Q3333CLM_abs_det, one_mul,
    T3333Deriv_eq_comp, ContinuousLinearMap.det, ContinuousLinearMap.coe_comp, LinearMap.det_comp,
    ← ContinuousLinearMap.det, ← ContinuousLinearMap.det, Frame3333Deriv_det, Kparam3333Deriv_det]
  obtain ⟨h0, h1, h2, h3, h4, h9⟩ := Kparam3333_eval u
  rw [h0, h1, h2, h3, h4, h9,
    show u 1 * (u 1 * u 2 * u 3 + u 4) - u 1 * u 2 * (u 1 * u 3) = u 1 * u 4 from by ring]
  simp only [abs_mul, abs_pow]
  ring

/-! ## `phi3333` is injective off the four pivot axes (the triangular coordinate recovery)

Off `{u 0 = 0} ∪ {u 1 = 0} ∪ {u 4 = 0} ∪ {u 9 = 0}`, `chartParams3333` is injective: every coordinate
is recovered from the matrix entries — direct reads, single divisions by `u 1`/`u 9`/`u 0`, and the two
`2×2` A-frame systems `(u 7, u 8)` / `(u 5, u 6)`, each of determinant `u 1·u 4 ≠ 0`. -/

set_option maxHeartbeats 1600000 in
/-- **`chartParams3333` is injective off `{u 0=0}∪{u 1=0}∪{u 4=0}∪{u 9=0}`** (triangular recovery). -/
theorem chartParams3333_injOn :
    Set.InjOn chartParams3333
      {u : Fin 27 → ℝ | u 0 ≠ 0 ∧ u 1 ≠ 0 ∧ u 4 ≠ 0 ∧ u 9 ≠ 0} := by
  rintro u ⟨hu0, hu1, hu4, hu9⟩ v ⟨hv0, hv1, hv4, hv9⟩ huv
  have hA : chartA3333 u = chartA3333 v := congrFun huv 0
  have hB : chartB3333 u = chartB3333 v := congrFun huv 1
  have hC : chartC3333 u = chartC3333 v := congrFun huv 2
  have eA := fun i j => congrFun (congrFun hA i) j
  have eB := fun i j => congrFun (congrFun hB i) j
  have eC := fun i j => congrFun (congrFun hC i) j
  have h1 : u 1 = v 1 := by have := eA 0 0; simpa [chartA3333] using this
  have h15 : u 15 = v 15 := by have := eB 2 0; simpa [chartB3333] using this
  have h16 : u 16 = v 16 := by have := eB 2 1; simpa [chartB3333] using this
  have h17 : u 17 = v 17 := by have := eB 2 2; simpa [chartB3333] using this
  have h18 : u 18 = v 18 := by have := eC 1 0; simpa [chartC3333] using this
  have h19 : u 19 = v 19 := by have := eC 1 1; simpa [chartC3333] using this
  have h20 : u 20 = v 20 := by have := eC 1 2; simpa [chartC3333] using this
  have h21 : u 21 = v 21 := by have := eC 2 0; simpa [chartC3333] using this
  have h22 : u 22 = v 22 := by have := eC 2 1; simpa [chartC3333] using this
  have h23 : u 23 = v 23 := by have := eC 2 2; simpa [chartC3333] using this
  have h2 : u 2 = v 2 := by
    have he := eA 0 1; simp only [chartA3333, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val] at he
    rw [h1] at he; exact mul_left_cancel₀ hv1 he
  have h3 : u 3 = v 3 := by
    have he := eA 1 0; simp only [chartA3333, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val] at he
    rw [h1] at he; exact mul_left_cancel₀ hv1 he
  have h4 : u 4 = v 4 := by
    have he := eA 1 1; simp only [chartA3333, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val] at he
    rw [h1, h2, h3] at he; linarith [he]
  have hx14 : v 1 * v 4 ≠ 0 := mul_ne_zero hv1 hv4
  have e02 := eA 0 2; have e12 := eA 1 2
  simp only [chartA3333, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.of_apply, Matrix.cons_val] at e02 e12
  simp only [h1, h2, h3, h4] at e02 e12
  have h7 : u 7 = v 7 := by
    have key : v 1 * v 4 * u 7 = v 1 * v 4 * v 7 := by
      linear_combination (v 1 * v 2 * v 3 + v 4) * e02 - v 1 * v 2 * e12
    exact mul_left_cancel₀ hx14 key
  have h8 : u 8 = v 8 := by
    have key : v 1 * v 4 * u 8 = v 1 * v 4 * v 8 := by
      linear_combination v 1 * e12 - v 1 * v 3 * e02
    exact mul_left_cancel₀ hx14 key
  have e20 := eA 2 0; have e21 := eA 2 1
  simp only [chartA3333, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.of_apply, Matrix.cons_val] at e20 e21
  simp only [h1, h2, h3, h4] at e20 e21
  have h5 : u 5 = v 5 := by
    have key : v 1 * v 4 * u 5 = v 1 * v 4 * v 5 := by
      linear_combination (v 1 * v 2 * v 3 + v 4) * e20 - v 1 * v 3 * e21
    exact mul_left_cancel₀ hx14 key
  have h6 : u 6 = v 6 := by
    have key : v 1 * v 4 * u 6 = v 1 * v 4 * v 6 := by
      linear_combination v 1 * e21 - v 1 * v 2 * e20
    exact mul_left_cancel₀ hx14 key
  have h0 : u 0 = v 0 := by
    have he := eA 2 2; simp only [chartA3333, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val] at he
    simp only [h1, h2, h3, h4, h5, h6, h7, h8] at he; linarith [he]
  have h9 : u 9 = v 9 := by
    have he := eB 0 0; simp only [chartB3333, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val] at he
    simp only [h7, h15] at he; linarith [he]
  have h11 : u 11 = v 11 := by
    have he := eB 0 1; simp only [chartB3333, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val] at he
    simp only [h7, h16, h9] at he
    have key : u 11 * v 9 = v 11 * v 9 := by linear_combination he
    exact mul_right_cancel₀ hv9 key
  have h12 : u 12 = v 12 := by
    have he := eB 0 2; simp only [chartB3333, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val] at he
    simp only [h7, h17, h9] at he
    have key : u 12 * v 9 = v 12 * v 9 := by linear_combination he
    exact mul_right_cancel₀ hv9 key
  have h10 : u 10 = v 10 := by
    have he := eB 1 0; simp only [chartB3333, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val] at he
    simp only [h8, h15, h9] at he
    have key : u 10 * v 9 = v 10 * v 9 := by linear_combination he
    exact mul_right_cancel₀ hv9 key
  have h13 : u 13 = v 13 := by
    have he := eB 1 1; simp only [chartB3333, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val] at he
    simp only [h8, h16, h9, h10, h11, h0] at he
    have key : v 0 * u 13 = v 0 * v 13 := by linear_combination he
    exact mul_left_cancel₀ hv0 key
  have h14 : u 14 = v 14 := by
    have he := eB 1 2; simp only [chartB3333, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val] at he
    simp only [h8, h17, h9, h10, h12, h0] at he
    have key : v 0 * u 14 = v 0 * v 14 := by linear_combination he
    exact mul_left_cancel₀ hv0 key
  have h24 : u 24 = v 24 := by
    have he := eC 0 0; simp only [chartC3333, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val] at he
    simp only [h11, h12, h18, h21, h0] at he
    have key : v 0 * u 24 = v 0 * v 24 := by linear_combination he
    exact mul_left_cancel₀ hv0 key
  have h25 : u 25 = v 25 := by
    have he := eC 0 1; simp only [chartC3333, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val] at he
    simp only [h11, h12, h19, h22, h0] at he
    have key : v 0 * u 25 = v 0 * v 25 := by linear_combination he
    exact mul_left_cancel₀ hv0 key
  have h26 : u 26 = v 26 := by
    have he := eC 0 2; simp only [chartC3333, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val] at he
    simp only [h11, h12, h20, h23, h0] at he
    have key : v 0 * u 26 = v 0 * v 26 := by linear_combination he
    exact mul_left_cancel₀ hv0 key
  funext j; fin_cases j <;>
    first
      | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | exact h6 | exact h7
      | exact h8 | exact h9 | exact h10 | exact h11 | exact h12 | exact h13 | exact h14 | exact h15
      | exact h16 | exact h17 | exact h18 | exact h19 | exact h20 | exact h21 | exact h22 | exact h23
      | exact h24 | exact h25 | exact h26

/-- **`phi3333` is injective off `{u 0=0}∪{u 1=0}∪{u 4=0}∪{u 9=0}`** (`paramsEquivFlat` a bijection
∘ `chartParams3333_injOn`). -/
theorem phi3333_injOn :
    Set.InjOn phi3333 {u : Fin 27 → ℝ | u 0 ≠ 0 ∧ u 1 ≠ 0 ∧ u 4 ≠ 0 ∧ u 9 ≠ 0} := by
  intro u hu v hv huv
  exact chartParams3333_injOn hu hv ((paramsEquivFlat M3333).injective huv)

/-! ## The genuine geometric change-of-variables for `phi3333` (the `cov` field)

`phi3333` is `InjOn` off `{u 0=0}∪{u 1=0}∪{u 4=0}∪{u 9=0}` (`phi3333_injOn`), C¹
(`phi3333_hasFDerivAt`), with structural determinant `|det Dφ| = |u 0|⁵·|u 1|⁴·|u 4|²·|u 9|³`
(`phi3333_abs_det`). The c-o-v runs on `V \ {u 0=0}` minus the three extra pivot slices (where
`phi3333` is `InjOn`), then adds them back as a FOUR-axis (here three-extra-slice) null contribution. -/

/-- The extra-axes slice image is null: a C¹ image of `(V\{u0=0}) ∩ ({u1=0}∪{u4=0}∪{u9=0})`. -/
theorem phi3333_slice_image_null (V : Set (Fin 27 → ℝ)) :
    (volume : Measure (Fin 27 → ℝ))
        (phi3333 '' ((V \ {x | x 0 = 0}) ∩
          ({x | x 1 = 0} ∪ {x | x 4 = 0} ∪ {x | x 9 = 0}))) = 0 := by
  refine MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    differentiable_phi3333.differentiableOn ?_
  refine measure_mono_null Set.inter_subset_right ?_
  exact measure_union_null (measure_union_null (coordZero_null 1) (coordZero_null 4))
    (coordZero_null 9)

set_option maxHeartbeats 1600000 in
/-- **The genuine geometric change-of-variables for `phi3333`** (the `cov` field, sorry-free). The
Jacobian c-o-v (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`) on the punctured set off
`{u 0=0}∪{u 1=0}∪{u 4=0}∪{u 9=0}` (`phi3333_injOn`), with `|det Dφ| = |u 0|⁵·|u 1|⁴·|u 4|²·|u 9|³`
(`phi3333_abs_det`), plus the two-sided null-slice add-back of the three extra pivot axes. -/
theorem phi3333_cov (V : Set (Fin 27 → ℝ)) (hV : MeasurableSet V) (g : (Fin 27 → ℝ) → ℝ≥0∞) :
    ∫⁻ x in phi3333 '' (V \ {x | x 0 = 0}), g x
      = ∫⁻ u in V \ {x | x 0 = 0}, ENNReal.ofReal (∏ j, |u j| ^ (leafH3333 j)) * g (phi3333 u) := by
  set S := V \ {x : Fin 27 → ℝ | x 0 = 0} with hS
  set E := ({x : Fin 27 → ℝ | x 1 = 0} ∪ {x | x 4 = 0} ∪ {x | x 9 = 0}) with hE
  set Sg := S \ E with hSg
  have hEmeas : MeasurableSet E :=
    ((measurableSet_eq_fun (measurable_pi_apply 1) measurable_const).union
      (measurableSet_eq_fun (measurable_pi_apply 4) measurable_const)).union
      (measurableSet_eq_fun (measurable_pi_apply 9) measurable_const)
  have hSmeas : MeasurableSet S :=
    hV.diff (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const)
  have hSgmeas : MeasurableSet Sg := hSmeas.diff hEmeas
  have hEnull : (volume : Measure (Fin 27 → ℝ)) E = 0 :=
    measure_union_null (measure_union_null (coordZero_null 1) (coordZero_null 4)) (coordZero_null 9)
  have hcov : ∫⁻ x in phi3333 '' Sg, g x
      = ∫⁻ u in Sg, ENNReal.ofReal |(phi3333Deriv u).det| * g (phi3333 u) := by
    refine lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSgmeas
      (fun x _ => (phi3333_hasFDerivAt x).hasFDerivWithinAt) ?_ g
    intro x hx y hy hxy
    refine phi3333_injOn ⟨hx.1.2, ?_, ?_, ?_⟩ ⟨hy.1.2, ?_, ?_, ?_⟩ hxy
    · exact fun h => hx.2 (Or.inl (Or.inl h))
    · exact fun h => hx.2 (Or.inl (Or.inr h))
    · exact fun h => hx.2 (Or.inr h)
    · exact fun h => hy.2 (Or.inl (Or.inl h))
    · exact fun h => hy.2 (Or.inl (Or.inr h))
    · exact fun h => hy.2 (Or.inr h)
  have hcov' : ∫⁻ x in phi3333 '' Sg, g x
      = ∫⁻ u in Sg, ENNReal.ofReal (∏ j, |u j| ^ (leafH3333 j)) * g (phi3333 u) := by
    rw [hcov]; refine setLIntegral_congr_fun hSgmeas (fun u _ => ?_)
    rw [phi3333_abs_det, leafH3333_prod_eq]
  have hLHS : ∫⁻ x in phi3333 '' S, g x = ∫⁻ x in phi3333 '' Sg, g x := by
    refine setLIntegral_congr ?_
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null ?_ (phi3333_slice_image_null V)
      rintro y ⟨⟨x, hxS, rfl⟩, hy⟩
      by_cases hxE : x ∈ E
      · exact ⟨x, ⟨hxS, hxE⟩, rfl⟩
      · exact absurd ⟨x, ⟨hxS, hxE⟩, rfl⟩ hy
    · rw [show phi3333 '' Sg \ phi3333 '' S = ∅ from by
        rw [Set.diff_eq_empty]; exact Set.image_mono Set.diff_subset]
      exact measure_empty
  have hRHS : ∫⁻ u in Sg, ENNReal.ofReal (∏ j, |u j| ^ (leafH3333 j)) * g (phi3333 u)
      = ∫⁻ u in S, ENNReal.ofReal (∏ j, |u j| ^ (leafH3333 j)) * g (phi3333 u) := by
    refine setLIntegral_congr (MeasureTheory.diff_ae_eq_self.2 ?_)
    exact measure_mono_null Set.inter_subset_right hEnull
  rw [hLHS, hcov', hRHS]

/-! ## The `NodeAchieverChart M3333` instance + the achiever box-divergence atom -/

/-- **The `(3,3,3,3)` achiever chart bundle** — the decisive multi-pivot `L = 3` node (LDU-core +
`B/C`-chaining), binding axis `0`, unit `Vval3333` (a genuine polynomial), the multi-pivot Jacobian
`|u 0|⁵·|u 1|⁴·|u 4|²·|u 9|³`. All fields banked sorry-free in `RouteM3333` except the genuine c-o-v
(`phi3333_cov`, resting on `phi3333_abs_det` = `Frame3333Deriv_det` ∘ `Kparam3333Deriv_det` ∘ the
measure-preserving `Q3333CLM_abs_det`, and `phi3333_injOn` = the triangular coord recovery). -/
noncomputable def nodeChart3333 : NodeAchieverChart M3333 where
  hpos := by rw [minAdm_M3333]; norm_num
  phi := phi3333
  p := (0 : Fin 27)
  leafH := leafH3333
  leafH_pivot := leafH3333_pivot
  Ufun := Vval3333
  Ubound := fun δ => by
    obtain ⟨B, hB0, hBle⟩ := Vval3333_le_on_box δ
    exact ⟨B, hB0, hBle, ae_restrict_of_ae Vval3333_ae_pos⟩
  Umeas := continuous_Vval3333.measurable
  leaf_integrand := leaf_integrand3333
  cov := phi3333_cov
  image_subset := phi3333_image_subset_cubeBox

/-- **`routeMCore_box_diverges_achiever` for `M = (3,3,3,3)`** — the achiever-path box-divergence atom
discharged at the DECISIVE multi-pivot `L = 3` node `(3,3,3,3)` (nonzero intermediate codims), stated
in the atom's own shape. The instance via the genuine chart bundle `nodeChart3333` fed through the
M-agnostic assembly `routeMCore_box_diverges_of_nodeChart`. NOT the general-`M` atom. -/
theorem routeMCore_box_diverges_achiever_3333 (c' : NNReal)
    (hc' : (minAdm M3333 : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M3333) ε,
      ENNReal.ofReal (|routeMCore M3333 x| ^ (-(c' : ℝ))) = ⊤ :=
  routeMCore_box_diverges_of_nodeChart M3333 nodeChart3333 c' hc' ε hε

end DLNFibre.DLN.RLCT
