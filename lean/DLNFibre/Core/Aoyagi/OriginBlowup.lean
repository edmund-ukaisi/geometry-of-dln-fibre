import DLNFibre.Core.Aoyagi.ResolutionInhabited

/-!
# `Core.Aoyagi.OriginBlowup` — leaf-2: the general-`Fin D` origin blow-up

The reusable coordinate-centre blow-up atom (Codex leaf-2), over a GENERAL ambient dimension
`Fin D`: the `D`-chart resolution of the coordinate family `F = (u₀,…,u_{D-1})` (`∑Fᵢ² = ‖u‖²`,
the maximal-ideal singularity). The universal Jacobian det `jacDet (blowupMap i) w = (w i)^(D-1)`
is proven for ALL `D`, so it INSTANTIATES at any dimension (e.g. `D = flatDim d`) with no
opaque-width `fin_cases`. This is the shared atom rung (B) and the monument's blow-up step need.
-/

open MeasureTheory Set Filter Topology RLCT

namespace DLNFibre.Core.Aoyagi

variable {D : ℕ}

/-- The origin blow-up chart map with pivot `i`: slot `i ↦ wᵢ`, slot `j ≠ i ↦ wᵢ·wⱼ`. -/
def blowupMap (i : Fin D) : (Fin D → ℝ) → (Fin D → ℝ) :=
  fun w j ↦ if j = i then w i else w i * w j

/-- The Jacobian `ContinuousLinearMap` of `blowupMap i` at `w`. -/
noncomputable def blowupDeriv (i : Fin D) (w : Fin D → ℝ) :
    (Fin D → ℝ) →L[ℝ] (Fin D → ℝ) :=
  ContinuousLinearMap.pi (fun j ↦ if j = i then ContinuousLinearMap.proj i
    else (w i) • ContinuousLinearMap.proj j + (w j) • ContinuousLinearMap.proj i)

theorem hasFDerivAt_blowupMap (i : Fin D) (w : Fin D → ℝ) :
    HasFDerivAt (blowupMap i) (blowupDeriv i w) w := by
  rw [blowupDeriv, hasFDerivAt_pi]
  intro j
  by_cases hj : j = i
  · have hf : (fun w : Fin D → ℝ ↦ blowupMap i w j) = fun w ↦ w i := by
      funext w; simp [blowupMap, hj]
    rw [hf, if_pos hj]
    exact hasFDerivAt_apply i w
  · have hf : (fun w : Fin D → ℝ ↦ blowupMap i w j) = fun w ↦ w i * w j := by
      funext w; simp [blowupMap, hj]
    rw [hf, if_neg hj]
    exact (hasFDerivAt_apply i w).mul (hasFDerivAt_apply j w)

/-- The entries of the Jacobian matrix of `blowupMap i` at `w`. -/
theorem toMatrix'_blowupDeriv (i : Fin D) (w : Fin D → ℝ) (a c : Fin D) :
    LinearMap.toMatrix' (blowupDeriv i w).toLinearMap a c =
      if a = i then (if i = c then 1 else 0)
      else (w i * (if a = c then 1 else 0) + w a * (if i = c then 1 else 0)) := by
  rw [LinearMap.toMatrix'_apply]
  by_cases ha : a = i
  · subst ha
    simp [blowupDeriv, Pi.single_apply]
  · simp [blowupDeriv, Pi.single_apply, ha]

/-- **The universal Jacobian determinant** `jacDet (blowupMap i) w = (w i)^(D-1)` (`2 ≤ D`). -/
theorem jacDet_blowupMap (hD : 2 ≤ D) (i : Fin D) (w : Fin D → ℝ) :
    jacDet (blowupMap i) w = (w i) ^ (D - 1) := by
  unfold jacDet
  rw [(hasFDerivAt_blowupMap i w).fderiv, ← LinearMap.det_toMatrix' (blowupDeriv i w).toLinearMap]
  set M := LinearMap.toMatrix' (blowupDeriv i w).toLinearMap with hMdef
  -- block-triangular splitter: pivot row `i` is its own singleton block (`1`); the rest is `wᵢ•I`.
  set b : Fin D → ℕ := fun a ↦ if a = i then 1 else 0 with hb
  have hbt : M.BlockTriangular b := by
    intro a c hlt
    have hai : a = i := by by_contra h; simp [hb, h] at hlt
    have hci : c ≠ i := by rintro rfl; simp [hb, hai] at hlt
    rw [hMdef, toMatrix'_blowupDeriv]
    subst hai
    simp [Ne.symm hci]
  rw [hbt.det]
  -- the image of `b` is `{0, 1}` (some `a ≠ i` exists since `2 ≤ D`).
  obtain ⟨a₀, ha₀⟩ : ∃ a : Fin D, a ≠ i := by
    have : 1 < Fintype.card (Fin D) := by simpa using hD
    obtain ⟨a₀, ha₀⟩ := Fintype.exists_ne_of_one_lt_card this i
    exact ⟨a₀, ha₀⟩
  have himg : Finset.univ.image b = {0, 1} := by
    apply Finset.Subset.antisymm
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨a, rfl⟩ := hx
      by_cases h : a = i <;> simp [hb, h]
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_image.2 ⟨a₀, Finset.mem_univ _, by simp [hb, ha₀]⟩
      · exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, by simp [hb]⟩
  rw [himg, Finset.prod_pair (by norm_num : (0 : ℕ) ≠ 1)]
  -- the pivot block `{i}` is `[1]`; the residual block is `wᵢ • I` on `{a ≠ i}`.
  have hblk1 : (M.toSquareBlock b 1).det = 1 := by
    have h1 : M.toSquareBlock b 1 = 1 := by
      ext p q
      have hp : (p : Fin D) = i := by
        have := p.2; simp only [hb] at this; by_contra h; simp [h] at this
      have hq : (q : Fin D) = i := by
        have := q.2; simp only [hb] at this; by_contra h; simp [h] at this
      have hpq : p = q := Subtype.ext (hp.trans hq.symm)
      rw [hpq, Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.one_apply_eq,
        hMdef, toMatrix'_blowupDeriv, hq]
      simp
    rw [h1, Matrix.det_one]
  have hblk0 : (M.toSquareBlock b 0).det = (w i) ^ (D - 1) := by
    have hEq : M.toSquareBlock b 0 = (w i) • (1 : Matrix _ _ ℝ) := by
      ext p q
      have hp : (p : Fin D) ≠ i := by
        have := p.2; simp only [hb] at this; by_contra h; simp [h] at this
      have hq : (q : Fin D) ≠ i := by
        have := q.2; simp only [hb] at this; by_contra h; simp [h] at this
      rw [Matrix.toSquareBlock_def, Matrix.of_apply, hMdef, toMatrix'_blowupDeriv]
      simp only [hp, if_false, Ne.symm hq, mul_zero, add_zero, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul, mul_ite, mul_one]
      by_cases hpq : (p : Fin D) = (q : Fin D)
      · rw [if_pos hpq, if_pos (Subtype.ext hpq)]
      · rw [if_neg hpq, if_neg (fun h ↦ hpq (Subtype.ext_iff.1 h))]
    rw [hEq, Matrix.det_smul, Matrix.det_one, mul_one]
    congr 1
    rw [Fintype.card_subtype]
    have hcard : (Finset.univ.filter fun a : Fin D ↦ b a = 0) = Finset.univ.erase i := by
      ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, hb]
      by_cases h : a = i <;> simp [h]
    rw [hcard, Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
  rw [hblk0, hblk1, mul_one]

end DLNFibre.Core.Aoyagi
