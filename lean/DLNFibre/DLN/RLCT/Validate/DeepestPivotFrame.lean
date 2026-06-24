import DLNFibre.DLN.RLCT.Validate.DeepestSplitReindex
import DLNFibre.DLN.RLCT.Validate.DeepestFrame
import DLNFibre.DLN.RLCT.Validate.DeepestFrameRaw

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestPivotFrame` — the pivot-aligned boundary frame fact (PIN1 (a))

The frame fact target (a) of the L2-PIN1 re-architecture: for a rank-`r` matrix `A` whose tail rows
vanish (the deepest last layer), there is a `B`-determined pivot column set `J` and a UNIT frame `Q`
such that the lower-right block of `Q` — read under the SAME pivot split `pivotThresholdSplit r b J` —
is a unit. This is the `B22`-invertibility input PIN1's `deepestEPivot_regSlice_fderiv` needs to build
the invertible reg-slice fderiv `F` (the second factor `det F = (det A)^{H_L−r}·(det B22)^r`).

The construction is the EXPLICIT pivot-aligned frame (Codex `xhigh` design-validated, construction (I)):
with the pivot columns `VJ` of the row factor `V` (the top `r` rows of `A`) a unit, the split-coordinate
frame `Q̃ := fromBlocks VJ⁻¹ (−VJ⁻¹·VK) 0 1` carries `V` to the pivot-aligned corner `[I_r | 0]` and has
`toBlocks₂₂ = 1` (trivially a unit). The actual frame is `Q := reindex e.symm e.symm Q̃` (so
`reindex e e Q = Q̃`). This SIDESTEPS the keystone `toBlocks22_isUnit_of_pivot_corner` — the explicit
frame realises `B22 = 1` directly, rather than reading it off a generic right-only normal form (whose
₂₂-block is singular precisely when `B`'s pivots are not front: the `corM`-vs-pivot indexing mismatch
that the generic `rank_normal_form_right_only` frame falls into for non-pivot-front `B`).

The pivot-set `J` is `B`-DETERMINED (`exists_pivot_cols_of_rank` of the row factor), so there is NO
restriction on the rank-`r` target. The same `J` must thread into PIN1's residual split and PIN2's
target normalization — that coordinated chart threading is the genuinely-large remaining step; this
module banks the standalone frame algebra it stands on.
-/

open Matrix
namespace DLNFibre.DLN.RLCT

open scoped Matrix

/-- **The σ-permutation bridge** for the pivot-column unit. `exists_pivot_cols_of_rank` gives
`IsUnit (V.submatrix id J)` with `J` in `J`'s own order, but `pivotThresholdSplit`'s left block
enumerates the pivots in SORTED order (`(pivotSupport r b J).orderEmbOfFin`). The two enumerations of
`Set.range J` differ by a permutation `σ : Fin r ≃ Fin r`. This produces `σ` with
`J (σ k) = (pivotThresholdSplit r b ha J).symm (Sum.inl k)` (the `k`-th sorted pivot), so the
sorted-column submatrix is a unit by `isUnit_submatrix_equiv`. -/
private theorem exists_sigma_sorted_pivot {r b : ℕ} (ha : r ≤ b) (J : Fin r ↪ Fin b) :
    ∃ σ : Fin r ≃ Fin r,
      ∀ k : Fin r, J (σ k) = (pivotThresholdSplit r b ha J).symm (Sum.inl k) := by
  classical
  -- The sorted-pivot enumeration `s k := (pivotThresholdSplit … J).symm (inl k)`.
  set s : Fin r → Fin b := fun k => (pivotThresholdSplit r b ha J).symm (Sum.inl k) with hs
  -- Every `s k` is a pivot column, so `s = J ∘ (a choice function)`. Build `σ` from injectivity +
  -- the shared range.
  -- `s k ∈ Set.range J`.
  have hmem : ∀ k, s k ∈ Set.range J := fun k =>
    pivotThresholdSplit_symm_inl_mem_range r b ha J k
  -- `σ k := J⁻¹ (s k)` via `Function.Embedding.toEquivRange`.
  let σ : Fin r → Fin r := fun k => J.toEquivRange.symm ⟨s k, hmem k⟩
  -- `J (σ k) = s k`. `J (σ k) = ↑(J.toEquivRange (σ k))` and the latter is `⟨s k, _⟩` by
  -- `apply_symm_apply`, whose coercion is `s k`.
  have hJσ : ∀ k, J (σ k) = s k := by
    intro k
    have hcoe : (J.toEquivRange (σ k) : Fin b) = J (σ k) :=
      congrArg Subtype.val (Function.Embedding.toEquivRange_apply J (σ k))
    have happ : J.toEquivRange (σ k) = ⟨s k, hmem k⟩ := Equiv.apply_symm_apply _ _
    rw [← hcoe, happ]
  -- `σ` is injective (`J` injective, `s` injective from the `.symm (inl ·)` being injective).
  have hσinj : Function.Injective σ := by
    intro k₁ k₂ h
    have : J (σ k₁) = J (σ k₂) := by rw [h]
    rw [hJσ, hJσ] at this
    -- `s` injective: `.symm` injective + `Sum.inl` injective.
    have hsi : s k₁ = s k₂ := this
    have := (Equiv.injective _ hsi : Sum.inl k₁ = Sum.inl k₂)
    exact Sum.inl_injective this
  -- A self-injection of a Fintype is a bijection ⟹ an Equiv.
  let σE : Fin r ≃ Fin r := Equiv.ofBijective σ ⟨hσinj, Finite.injective_iff_surjective.mp hσinj⟩
  exact ⟨σE, fun k => hJσ k⟩

/-- **The pivot columns of `V` form a unit** (the `VJ`-unit, with `VJ` read under the SORTED pivot
order of `pivotThresholdSplit`). Given `IsUnit (V.submatrix id J)` (the `J`-ordered pivot block from
`exists_pivot_cols_of_rank`), the matrix `of (fun i k => V i ((pivotThresholdSplit r b ha J).symm
(Sum.inl k)))` — `V`'s columns at the sorted pivots — is a unit, via the σ-bridge + `isUnit_submatrix_equiv`. -/
private theorem isUnit_pivotCols {r b : ℕ} (ha : r ≤ b)
    (V : Matrix (Fin r) (Fin b) ℝ) (J : Fin r ↪ Fin b)
    (hJ : IsUnit (V.submatrix (id : Fin r → Fin r) (J : Fin r → Fin b))) :
    IsUnit (Matrix.of (fun (i k : Fin r) =>
      V i ((pivotThresholdSplit r b ha J).symm (Sum.inl k)))) := by
  obtain ⟨σ, hσ⟩ := exists_sigma_sorted_pivot ha J
  -- The sorted-pivot block = the `J`-ordered block with columns permuted by `σ`.
  have heq : (Matrix.of (fun (i k : Fin r) =>
        V i ((pivotThresholdSplit r b ha J).symm (Sum.inl k))))
      = (V.submatrix (id : Fin r → Fin r) (J : Fin r → Fin b)).submatrix
          (id : Fin r → Fin r) (σ : Fin r → Fin r) := by
    ext i k
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id_eq]
    rw [← hσ k]
  rw [heq]
  exact (Matrix.isUnit_submatrix_equiv (Equiv.refl _) σ).mpr hJ

/-- **`V.rank = r` for the top-`r`-rows row factor.** If `A : Fin a × Fin b` has rank `r` and its
tail rows (index `≥ r`) vanish, the top-`r`-rows submatrix `V := A.submatrix (Fin.castLE) id` also has
rank `r`. `≤` is `rank_submatrix_le`; `≥` because `A` factors as the zero-extension of `V` (tail rows
zero), so `A.mulVecLin = ι ∘ V.mulVecLin` with `ι` the zero-padding embedding, giving
`rank A ≤ rank V`. -/
private theorem rank_topRows {a b r : ℕ} (hra : r ≤ a)
    (A : Matrix (Fin a) (Fin b) ℝ) (hA : A.rank = r)
    (htail : ∀ (i : Fin a) (j : Fin b), r ≤ (i : ℕ) → A i j = 0) :
    (A.submatrix (Fin.castLE hra : Fin r → Fin a) (id : Fin b → Fin b)).rank = r := by
  -- `V.rank ≤ A.rank = r`.
  have hle : (A.submatrix (Fin.castLE hra : Fin r → Fin a) (id : Fin b → Fin b)).rank ≤ r :=
    hA ▸ Matrix.rank_submatrix_le (Fin.castLE hra) (Equiv.refl _) A
  -- The zero-padding embedding `ι : (Fin r → ℝ) →ₗ (Fin a → ℝ)`, `ι v i = if i<r then v ⟨i,_⟩ else 0`.
  let ι : (Fin r → ℝ) →ₗ[ℝ] (Fin a → ℝ) :=
    { toFun := fun v i => if h : (i : ℕ) < r then v ⟨i, h⟩ else 0
      map_add' := by intro v w; funext i; by_cases h : (i : ℕ) < r <;> simp [h]
      map_smul' := by intro c v; funext i; by_cases h : (i : ℕ) < r <;> simp [h] }
  -- `A.mulVecLin = ι ∘ V.mulVecLin`: at row `i < r`, `(A *ᵥ x) i = (V *ᵥ x) ⟨i,_⟩`; at `i ≥ r`, `0`.
  have hcomp : A.mulVecLin
      = ι.comp (A.submatrix (Fin.castLE hra : Fin r → Fin a) (id : Fin b → Fin b)).mulVecLin := by
    apply LinearMap.ext; intro x; funext i
    simp only [Matrix.mulVecLin_apply, LinearMap.comp_apply, ι, LinearMap.coe_mk, AddHom.coe_mk]
    by_cases h : (i : ℕ) < r
    · rw [dif_pos h]
      simp only [Matrix.mulVec, Matrix.submatrix_apply, id_eq, dotProduct]
      congr 1
    · rw [dif_neg h]
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro j _
      rw [htail i j (by omega), zero_mul]
  -- `rank A = finrank (range A.mulVecLin) ≤ finrank (range V.mulVecLin) = rank V` via `range_comp`.
  have hge : A.rank ≤ (A.submatrix (Fin.castLE hra : Fin r → Fin a) (id : Fin b → Fin b)).rank := by
    show Module.finrank ℝ (LinearMap.range A.mulVecLin) ≤ _
    rw [hcomp, LinearMap.range_comp]
    exact Submodule.finrank_map_le ι _
  rw [hA] at hge
  omega

/-- **The pivot-aligned boundary frame fact** (PIN1 (a)). For a rank-`r` matrix `A : Fin a × Fin b`
whose tail rows vanish (`A i j = 0` for `(i:ℕ) ≥ r`), there is a `B`-determined pivot column set
`J : Fin r ↪ Fin b` and a UNIT frame `Q : Fin b × Fin b` such that:
- the lower-right block of `Q` under the pivot split `e := pivotThresholdSplit r b ha J` is a unit
  (`IsUnit ((reindex e e Q).toBlocks₂₂)`) — the `B22`-invertibility PIN1 needs; AND
- `A · Q` is the block-normal corner in split coordinates:
  `reindex (rThresholdSplit r a haA) e (A * Q) = fromBlocks 1 0 0 0`.

Construction (Codex `xhigh` design (I)): `Q := reindex e.symm e.symm (fromBlocks VJ⁻¹ (−VJ⁻¹·VK) 0 1)`,
with `VJ`/`VK` the pivot/complement columns of the top-`r`-rows row factor `V`. Then `reindex e e Q` is
the explicit block frame, `toBlocks₂₂ = 1` (a unit), and `V · Q` is the pivot-aligned `[I_r | 0]` —
realising `B22 = 1` directly, with NO restriction on the rank-`r` `A` (the `corM`-vs-pivot mismatch of a
generic right-only normal form is avoided). Network-free; the deepest last layer instantiates it. -/
theorem exists_pivotFrame_lastBlock_isUnit {a b r : ℕ} (ha : r ≤ b) (hra : r ≤ a)
    (A : Matrix (Fin a) (Fin b) ℝ) (hA : A.rank = r)
    (htail : ∀ (i : Fin a) (j : Fin b), r ≤ (i : ℕ) → A i j = 0) :
    ∃ (J : Fin r ↪ Fin b) (Q : Matrix (Fin b) (Fin b) ℝ),
      IsUnit Q ∧
      IsUnit ((Matrix.reindex (pivotThresholdSplit r b ha J)
          (pivotThresholdSplit r b ha J) Q).toBlocks₂₂) ∧
      Matrix.reindex (rThresholdSplit r a hra) (pivotThresholdSplit r b ha J) (A * Q)
        = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 := by
  classical
  -- The top-`r`-rows row factor `V` and its pivot column set `J`.
  set V : Matrix (Fin r) (Fin b) ℝ := A.submatrix (Fin.castLE hra) id with hV
  have hVrank : V.rank = r := rank_topRows hra A hA htail
  obtain ⟨J, hJ⟩ := Core.Matrix.exists_pivot_cols_of_rank V hVrank
  set e := pivotThresholdSplit r b ha J with he
  -- The pivot / complement column blocks of `V` (in sorted order).
  set VJ : Matrix (Fin r) (Fin r) ℝ :=
    Matrix.of (fun (i k : Fin r) => V i (e.symm (Sum.inl k))) with hVJ
  set VK : Matrix (Fin r) (Fin (b - r)) ℝ :=
    Matrix.of (fun (i : Fin r) (k : Fin (b - r)) => V i (e.symm (Sum.inr k))) with hVK
  have hVJunit : IsUnit VJ := isUnit_pivotCols ha V J hJ
  have hVJdet : IsUnit VJ.det := Matrix.isUnit_iff_isUnit_det _ |>.mp hVJunit
  -- The explicit split-coordinate frame `Q̃ = [[VJ⁻¹, −VJ⁻¹·VK], [0, 1]]`.
  set Qt : Matrix (Fin r ⊕ Fin (b - r)) (Fin r ⊕ Fin (b - r)) ℝ :=
    Matrix.fromBlocks VJ⁻¹ (-(VJ⁻¹ * VK)) 0 1 with hQt
  -- `Q̃` is a unit (block-triangular, `VJ⁻¹` and `1` units).
  have hQtunit : IsUnit Qt := by
    rw [hQt]
    exact Matrix.isUnit_fromBlocks_zero₂₁.mpr
      ⟨(Matrix.isUnit_nonsing_inv_iff).mpr hVJunit, isUnit_one⟩
  -- The actual frame `Q := reindex e.symm e.symm Q̃` (so `reindex e e Q = Q̃`).
  refine ⟨J, Matrix.reindex e.symm e.symm Qt, ?_, ?_, ?_⟩
  · -- `IsUnit Q` from `IsUnit Q̃` (reindex is a unit-preserving submatrix by an equiv).
    rw [Matrix.reindex_apply, Equiv.symm_symm]
    exact (Matrix.isUnit_submatrix_equiv e e).mpr hQtunit
  · -- `reindex e e Q = Q̃`, so `toBlocks₂₂ = 1`.
    have hree : Matrix.reindex e e (Matrix.reindex e.symm e.symm Qt) = Qt := by
      rw [Matrix.reindex_apply, Matrix.reindex_apply, Equiv.symm_symm,
        Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]
    rw [hree, hQt, Matrix.toBlocks_fromBlocks₂₂]
    exact isUnit_one
  · -- The corner value `reindex (rThresholdSplit r a) e (A * Q) = fromBlocks 1 0 0 0`.
    -- `reindex e e Q = Q̃` (reused).
    have hree : Matrix.reindex e e (Matrix.reindex e.symm e.symm Qt) = Qt := by
      rw [Matrix.reindex_apply, Matrix.reindex_apply, Equiv.symm_symm,
        Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]
    -- Split the product on the shared middle index `Fin b` by `e.symm`:
    -- `reindex r1 e (A*Q) = (reindex r1 e A) * (reindex e e Q)`.
    have hsplit : Matrix.reindex (rThresholdSplit r a hra) e
          (A * Matrix.reindex e.symm e.symm Qt)
        = (Matrix.reindex (rThresholdSplit r a hra) e A)
            * (Matrix.reindex e e (Matrix.reindex e.symm e.symm Qt)) := by
      simp only [Matrix.reindex_apply, Equiv.symm_symm]
      exact (Matrix.submatrix_mul_equiv A (Qt.submatrix e e)
          (rThresholdSplit r a hra).symm (e.symm) e.symm).symm
    rw [hsplit, hree]
    -- `reindex r1 e A = fromBlocks VJ VK 0 0` (top rows are `V`'s pivot/complement cols, tail rows 0).
    have hA_blocks : Matrix.reindex (rThresholdSplit r a hra) e A
        = Matrix.fromBlocks VJ VK (0 : Matrix (Fin (a - r)) (Fin r) ℝ) 0 := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
          Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
          Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
          Matrix.zero_apply, hVJ, hVK, hV, Matrix.of_apply, id_eq]
      · rw [rThresholdSplit_symm_inl]
      · rw [rThresholdSplit_symm_inl]
      · rw [rThresholdSplit_symm_inr]; exact htail _ _ (by simp only [Fin.val_mk]; omega)
      · rw [rThresholdSplit_symm_inr]; exact htail _ _ (by simp only [Fin.val_mk]; omega)
    rw [hA_blocks, hQt, Matrix.fromBlocks_multiply]
    -- The four blocks: ₁₁ = VJ·VJ⁻¹ = 1; ₁₂ = VJ·(−VJ⁻¹VK)+VK = 0; ₂₁ = ₂₂ = 0.
    congr 1
    · rw [Matrix.mul_zero, add_zero, Matrix.mul_nonsing_inv VJ hVJdet]
    · rw [Matrix.mul_neg, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv VJ hVJdet,
        Matrix.one_mul, Matrix.mul_one, neg_add_cancel]
    · rw [Matrix.zero_mul, Matrix.zero_mul, add_zero]
    · rw [Matrix.zero_mul, Matrix.zero_mul, add_zero]

/-- **The deepest-point last-layer pivot frame** (the deepest-point instance of (a), `2 ≤ L`). At the
deepest point's last layer (tail rows vanish at `2 ≤ L`, rank exactly `r`), there is a `B`-determined
pivot column set `J` and a unit frame `Q` whose ₂₂-block under the pivot split is a unit, with the
last layer carried to the pivot-aligned corner. The deepest-point instantiation of
`exists_pivotFrame_lastBlock_isUnit`, with `A := deepestPoint … (lastLayer hL)`. This is the frame the
re-architected `deepestPoint_frame` last-layer arm must use (replacing the bare `rank_normal_form_right_only`,
whose ₂₂-block is singular for non-pivot-front `B`); the SAME `J` threads PIN1's residual split + PIN2's
target normalization. -/
theorem exists_deepest_lastLayer_pivotFrame {L : ℕ} (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L) :
    ∃ (J : Fin r ↪ Fin (H ((lastLayer hL).succ)))
      (Q : Matrix (Fin (H ((lastLayer hL).succ))) (Fin (H ((lastLayer hL).succ))) ℝ),
      IsUnit Q ∧
      IsUnit ((Matrix.reindex (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) J)
          (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) J) Q).toBlocks₂₂) ∧
      Matrix.reindex (rThresholdSplit r (H ((lastLayer hL).castSucc)) (hr _))
          (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) J)
          (deepestPoint H r B hB hr hL (lastLayer hL) * Q)
        = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 := by
  have hrank : (deepestPoint H r B hB hr hL (lastLayer hL)).rank = r :=
    (deepestPoint_isDeep H r B hB hr hL).2.1 (lastLayer hL)
  -- The last layer's tail ROWS vanish (`2 ≤ L`, `(lastLayer:ℕ)+1 = L`).
  have hsL : ((lastLayer hL : Fin L) : ℕ) + 1 = L := by simp only [lastLayer]; omega
  have htail : ∀ (i : Fin (H ((lastLayer hL).castSucc))) (j : Fin (H ((lastLayer hL).succ))),
      r ≤ (i : ℕ) → deepestPoint H r B hB hr hL (lastLayer hL) i j = 0 :=
    fun i j hi => (deepestPoint_isDeep H r B hB hr hL).2.2.2.2 (lastLayer hL) hL2 hsL i j hi
  exact exists_pivotFrame_lastBlock_isUnit (hr _) (hr _)
    (deepestPoint H r B hB hr hL (lastLayer hL)) hrank htail

end DLNFibre.DLN.RLCT
