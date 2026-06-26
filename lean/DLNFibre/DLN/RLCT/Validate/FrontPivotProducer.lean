import DLNFibre.DLN.RLCT.Validate.DeepestFramedProductPivot

/-!
# `DLNFibre.DLN.RLCT.Validate.FrontPivotProducer` — the front-pivot split alignment

The B (front-pivot WLOG) route for the L2 `hproducer` (b)-atom. Design cert:
`expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability/b-wlog-spec.md`.

The producer's (b)-conjunct `∑ deepestEFull² = Sreg` is FALSE for a non-front pivot `J` (the last
layer carries a column-permutation `π_J`). The deciding call (b-wlog-spec) is to run the chart with a
**FRONT** pivot — `J = frontEmbed := ⟨Fin.castLE _, _⟩`, the embedding `k ↦ k` — for which the pivot
split `pivotThresholdSplit … J` IS the threshold split `rThresholdSplit …` (banked
`pivotThresholdSplit_castLE`). Then `π_J = id`, the last-layer reads decode to threshold columns, and
the whole telescope is clean.

This module isolates the **two split-alignment facts** the front-pivot body needs:
- `pivotThresholdSplit_frontEmbed` — the OUTER pivot split (`Fin (H (Fin.last L))`) is the threshold
  split (a direct `pivotThresholdSplit_castLE` instance);
- `pivotThresholdSplit_pivotJSucc_frontEmbed` — the LAST-LAYER `.succ`-side pivot split
  (`Fin (H ((lastLayer hL).succ))`, indexed by `pivotJSucc J`) is the threshold split there too
  (`pivotJSucc frontEmbed` is the `.succ`-width castLE embedding, then `pivotThresholdSplit_castLE`).

Both are network-free index algebra (no `Params`, no `deepestSplit`). They are exactly the rewrites
that collapse `framedParamsPivot_last`'s pivot reindex to a threshold reindex, making the last-layer
frame relation clean (the `hS1'` that is refuted for general `J`).
-/

open Matrix Filter Topology
open scoped BigOperators
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The front pivot embedding** `Fin r ↪ Fin (H (Fin.last L))`, `k ↦ k` (the order embedding
`Fin.castLE`). Its pivot columns ARE the first `r`, so its pivot split is the threshold split. -/
noncomputable def frontEmbed (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s) :
    Fin r ↪ Fin (H (Fin.last L)) :=
  ⟨Fin.castLE (hr (Fin.last L)), Fin.castLE_injective (hr (Fin.last L))⟩

/-- **The outer front-pivot split IS the threshold split.** For `J = frontEmbed`, the pivot columns
are `{0,…,r−1}`, so `pivotThresholdSplit r (H (Fin.last L)) … (frontEmbed …)` coincides with
`rThresholdSplit r (H (Fin.last L)) …`. Direct `pivotThresholdSplit_castLE`. -/
theorem pivotThresholdSplit_frontEmbed (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) :
    pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) (frontEmbed H r hr)
      = rThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) :=
  pivotThresholdSplit_castLE r (H (Fin.last L)) (hr (Fin.last L))

/-- **`pivotJSucc` of the front pivot is the `.succ`-width front embedding.** `pivotJSucc J`
transports `J` along `finCongr (H_lastLayer_succ).symm` into `Fin (H ((lastLayer hL).succ))`; for
`J = frontEmbed` (`k ↦ k`) the transport is again `k ↦ k`, i.e. `Fin.castLE` into the `.succ` width.
The two casts `Fin.castLE (last L)` and `finCongr (H_lastLayer_succ)⁻¹` compose to
`Fin.castLE ((lastLayer).succ)`
on the value `↑k`. -/
theorem pivotJSucc_frontEmbed (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    pivotJSucc H r hL (frontEmbed H r hr)
      = ⟨Fin.castLE (hr ((lastLayer hL).succ)),
          Fin.castLE_injective (hr ((lastLayer hL).succ))⟩ := by
  apply Function.Embedding.ext
  intro k
  -- `pivotJSucc frontEmbed k = finCongr (…) (Fin.castLE … k)`; both sides have value `↑k`.
  simp only [pivotJSucc, frontEmbed, Function.Embedding.trans_apply,
    finCongr_apply, Function.Embedding.coeFn_mk]
  apply Fin.ext
  simp [Fin.castLE]

/-- **The last-layer `.succ`-side front-pivot split IS the threshold split.** For `J = frontEmbed`,
`pivotJSucc J` is the `.succ`-width front embedding (`pivotJSucc_frontEmbed`), so its pivot split is
the threshold split there (`pivotThresholdSplit_castLE`). The rewrite collapsing
`framedParamsPivot_last`'s column reindex to a threshold reindex. -/
theorem pivotThresholdSplit_pivotJSucc_frontEmbed (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _)
        (pivotJSucc H r hL (frontEmbed H r hr))
      = rThresholdSplit r (H ((lastLayer hL).succ)) (hr _) := by
  rw [pivotJSucc_frontEmbed H r hr hL]
  exact pivotThresholdSplit_castLE r (H ((lastLayer hL).succ)) (hr _)

/-! ## S5a — the producer's pivot block is eventually invertible

These were originally banked in `DeepestEFullSregComparability` (downstream of the cert); the
front-pivot producer body in `DeepestGaugeConstruction` consumes `eventually_P00_invertible`, so they
live here (upstream of the cert) instead. -/

/-- **S5a invertibility germ** (network-free). A continuous matrix-valued map `M : X → Matrix r r ℝ`
equal to the identity at a basepoint `x0` is invertible (`IsUnit`) on a neighborhood of `x0`. The
determinant `x ↦ (M x).det` is continuous (`Continuous.matrix_det`), `= (1).det = 1 ≠ 0` at `x0`,
so by `ContinuousAt.eventually_ne` the determinant is eventually nonzero, hence `M x` is a unit
(`Matrix.isUnit_iff_isUnit_det`). The abstract core of the producer's `det P00 ≠ 0` open set. -/
theorem eventually_isUnit_of_continuous_eq_one {X r : Type*} [TopologicalSpace X]
    [Fintype r] [DecidableEq r] {M : X → Matrix r r ℝ} (hM : Continuous M) {x0 : X}
    (hx0 : M x0 = 1) :
    ∀ᶠ x in 𝓝 x0, IsUnit (M x) := by
  have hdet : Continuous fun x => (M x).det := hM.matrix_det
  have hdet0 : (M x0).det = 1 := by rw [hx0]; simp
  have hne : (M x0).det ≠ 0 := by rw [hdet0]; exact one_ne_zero
  have hev : ∀ᶠ x in 𝓝 x0, (M x).det ≠ 0 :=
    (hdet.continuousAt).eventually_ne hne
  refine hev.mono (fun x hx => ?_)
  rw [Matrix.isUnit_iff_isUnit_det]
  exact Ne.isUnit hx

/-- The layer partial-product matrix is continuous in the parameters. Induction on chain length:
base `prodAux 0 = 1` constant; step `prodAux (k+1) = prodAux k * layer k`. -/
private theorem continuous_prodAux' (H : Fin (L + 1) → ℕ) (k : ℕ) (hk : k < L + 1) :
    Continuous (fun A : Params H => prodAux H A k hk) := by
  revert hk
  induction k with
  | zero =>
      intro hk
      simpa [prodAux] using
        (continuous_const :
          Continuous (fun _ : Params H => (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)))
  | succ k ih =>
      intro hk
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      let layer : Params H → Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ :=
        fun A => ((by rw [e1, e2]; exact A ⟨k, hkL⟩) :
          Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ)
      have hLayer : Continuous layer := by
        dsimp [layer]
        simpa only [e1, e2, eq_mpr_eq_cast, cast_eq] using
          (continuous_apply (⟨k, hkL⟩ : Fin L) :
            Continuous (fun A : Params H => A ⟨k, hkL⟩))
      have hMul : Continuous (fun A : Params H => prodAux H A k hk' * layer A) :=
        (ih hk').matrix_mul hLayer
      exact hMul.congr fun A => by dsimp [layer]; rfl

/-- The multiplication map `A ↦ prod H A` is continuous (`continuous_prodAux'` at `k = L`). -/
private theorem continuous_prod' (H : Fin (L + 1) → ℕ) : Continuous (prod H) :=
  continuous_prodAux' H L (Nat.lt_succ_self L)

/-- **The producer's `(1,1)`-block map is continuous in `w`.** `w ↦ (reindex e₁ e₂ (P0 · (prod
((paramsEquivFlat).symm w) − B) · QL)).toBlocks₁₁ + 1`. The flattening `(paramsEquivFlat).symm` is a
continuous linear equiv (`paramsEquivFlatCLE`), `prod` is continuous, the matrix algebra is entrywise
continuous. The continuity input to S5a invertibility. -/
theorem continuous_block₁₁_map (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ)
    (P0 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
    (QL : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ)
    (e₁ : Fin (H 0) ≃ Fin r ⊕ Fin (H 0 - r))
    (e₂ : Fin (H (Fin.last L)) ≃ Fin r ⊕ Fin (H (Fin.last L) - r)) :
    Continuous fun w : Fin (flatDim H) → ℝ =>
      (Matrix.reindex e₁ e₂
          (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₁₁
        + (1 : Matrix (Fin r) (Fin r) ℝ) := by
  have hsymmcoe : ⇑(paramsEquivFlatCLE H).symm = ⇑(paramsEquivFlat H).symm := by
    funext y
    apply (paramsEquivFlat H).injective
    rw [(paramsEquivFlat H).apply_symm_apply]
    have hcle : (paramsEquivFlat H) ((paramsEquivFlatCLE H).symm y)
        = (paramsEquivFlatCLE H) ((paramsEquivFlatCLE H).symm y) := by
      rw [← paramsEquivFlatCLE_coe H]
    rw [hcle, ContinuousLinearEquiv.apply_symm_apply]
  have hsymm : Continuous fun w : Fin (flatDim H) → ℝ => (paramsEquivFlat H).symm w := by
    rw [← hsymmcoe]; exact (paramsEquivFlatCLE H).symm.continuous
  have hprod : Continuous fun w : Fin (flatDim H) → ℝ => prod H ((paramsEquivFlat H).symm w) :=
    (continuous_prod' H).comp hsymm
  have hconj : Continuous fun w : Fin (flatDim H) → ℝ =>
      P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL :=
    (continuous_const.matrix_mul ((hprod.sub continuous_const))).matrix_mul continuous_const
  have hreindex : Continuous fun w : Fin (flatDim H) → ℝ =>
      Matrix.reindex e₁ e₂ (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL) :=
    hconj.matrix_reindex e₁ e₂
  exact (hreindex.matrix_submatrix Sum.inl Sum.inl).add continuous_const

/-- **S5a — the producer's pivot block is eventually invertible** (`hproducer` conjunct). The `(1,1)`
block `P00 w = (reindex e₁ e₂ (P0·(prod((symm) w) − B)·QL)).toBlocks₁₁ + 1` is `1` at the deepest point
`w0` (`prod ((symm) w0) = prod (deepestPoint) = B`, residual `0`), hence invertible on a neighborhood
(`continuous_block₁₁_map` + `eventually_isUnit_of_continuous_eq_one`). -/
theorem eventually_P00_invertible (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (P0 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
    (QL : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ)
    (e₁ : Fin (H 0) ≃ Fin r ⊕ Fin (H 0 - r))
    (e₂ : Fin (H (Fin.last L)) ≃ Fin r ⊕ Fin (H (Fin.last L) - r)) :
    ∀ᶠ w in 𝓝 ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
      IsUnit ((Matrix.reindex e₁ e₂
          (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₁₁
        + (1 : Matrix (Fin r) (Fin r) ℝ)) := by
  apply eventually_isUnit_of_continuous_eq_one (continuous_block₁₁_map H r B P0 QL e₁ e₂)
  have hsymm0 : (paramsEquivFlat H).symm ((paramsEquivFlat H) (deepestPoint H r B hB hr hL))
      = deepestPoint H r B hB hr hL := (paramsEquivFlat H).symm_apply_apply _
  have hprod0 : prod H (deepestPoint H r B hB hr hL) = B :=
    (deepestPoint_isDeep H r B hB hr hL).1
  rw [hsymm0, hprod0]
  have hz : P0 * (B - B) * QL = 0 := by rw [sub_self, Matrix.mul_zero, Matrix.zero_mul]
  rw [hz]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply,
    Matrix.zero_apply, Matrix.add_apply, zero_add]

end DLNFibre.DLN.RLCT
