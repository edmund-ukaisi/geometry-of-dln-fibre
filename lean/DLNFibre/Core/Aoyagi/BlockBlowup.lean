import DLNFibre.Core.Aoyagi.OriginBlowup

/-!
# `Core.Aoyagi.BlockBlowup` — the block-center blow-up atom (O9)

**BLUEPRINT (aoyagi-engine rung C; elder S1).** Aoyagi's interior blow-ups are BLOCK-CENTER
substitutions WITH SPECTATORS (worked.tex p.16/19): a center `S ⊆ Fin D` with pivot `p ∈ S`; the pivot
maps to `w_p`, the other center coordinates gain the pivot factor (`w_p·w_j`), and the SPECTATORS
(`∉ S`) are FIXED. The full-ambient `OriginBlowup.blowupMap` is the `S = univ` instance; using it for
interior steps is WRONG (a shear cannot undo spectator multiplication, and it forces the ambient−1
Jacobian exponent instead of the center-size−1 one — W2). This atom is what the coupled monument's
step maps (`Core.Aoyagi.PrincipalInv`, `σ = sh ∘ blockBlowupMap S p`) compose.

**Ownership.** `blockBlowupMap` + the easy structural lemmas are landed here (sorry-free). The two
Jacobian/injectivity facts (`jacDet_blockBlowupMap`, `injOn_blockBlowupMap`) are the O9 obligation —
signatures pinned here as `@[blueprint]` sorries for seat-w0l3 to PROVE IN PLACE (do NOT redefine the
atom). `jacDet = w_p^(|S|−1)` is the `BlockTriangular.det` pattern of `jacDet_blowupMap`, generalized
to `|S|`; it is `|S|`-general INCLUDING `|S| = 1` (`w_p^0 = 1`, the trivial `d ↦ u` step). These two
are OFF the composition driver's cone (consumed only inside L6's proof), so they are a separate leaf.
-/

open MeasureTheory Set Filter Topology RLCT

namespace DLNFibre.Core.Aoyagi

variable {D : ℕ}

/-- The **block-center blow-up** with center `S` and pivot `p ∈ S`: pivot `p ↦ w_p`; other center
coordinates `j ∈ S \ {p} ↦ w_p · w_j`; SPECTATORS `j ∉ S ↦ w_j` (fixed). `S = univ` is
`OriginBlowup.blowupMap p`; `S = {p}` is the identity (`w_p^0`, the trivial hypersurface step). -/
def blockBlowupMap (S : Finset (Fin D)) (p : Fin D) : (Fin D → ℝ) → (Fin D → ℝ) :=
  fun w j ↦ if j = p then w p else if j ∈ S then w p * w j else w j

/-- `blockBlowupMap S p` fixes the origin. -/
theorem blockBlowupMap_zero (S : Finset (Fin D)) (p : Fin D) :
    blockBlowupMap S p (0 : Fin D → ℝ) = 0 := by
  funext j
  simp only [blockBlowupMap, Pi.zero_apply, mul_zero, ite_self, ite_self]

/-- `blockBlowupMap S p` is continuous. -/
theorem continuous_blockBlowupMap (S : Finset (Fin D)) (p : Fin D) :
    Continuous (blockBlowupMap S p) := by
  refine continuous_pi (fun j ↦ ?_)
  by_cases hj : j = p
  · have : (fun w : Fin D → ℝ ↦ blockBlowupMap S p w j) = fun w ↦ w p := by
      funext w; simp [blockBlowupMap, hj]
    rw [this]; exact continuous_apply p
  · by_cases hjS : j ∈ S
    · have : (fun w : Fin D → ℝ ↦ blockBlowupMap S p w j) = fun w ↦ w p * w j := by
        funext w; simp [blockBlowupMap, hj, hjS]
      rw [this]; exact (continuous_apply p).mul (continuous_apply j)
    · have : (fun w : Fin D → ℝ ↦ blockBlowupMap S p w j) = fun w ↦ w j := by
        funext w; simp [blockBlowupMap, hj, hjS]
      rw [this]; exact continuous_apply j

/-- `blockBlowupMap S p` is analytic on the whole space (a polynomial map). -/
theorem analyticOnNhd_blockBlowupMap (S : Finset (Fin D)) (p : Fin D) :
    AnalyticOnNhd ℝ (blockBlowupMap S p) Set.univ := by
  have hproj : ∀ k : Fin D, AnalyticOnNhd ℝ (fun w : Fin D → ℝ ↦ w k) Set.univ := fun k ↦
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin D ↦ ℝ) k).analyticOnNhd _
  apply AnalyticOnNhd.pi
  intro j
  by_cases hj : j = p
  · have : (fun w : Fin D → ℝ ↦ blockBlowupMap S p w j) = fun w ↦ w p := by
      funext w; simp [blockBlowupMap, hj]
    rw [this]; exact hproj p
  · by_cases hjS : j ∈ S
    · have : (fun w : Fin D → ℝ ↦ blockBlowupMap S p w j) = fun w ↦ w p * w j := by
        funext w; simp [blockBlowupMap, hj, hjS]
      rw [this]; exact (hproj p).mul (hproj j)
    · have : (fun w : Fin D → ℝ ↦ blockBlowupMap S p w j) = fun w ↦ w j := by
        funext w; simp [blockBlowupMap, hj, hjS]
      rw [this]; exact hproj j

/-- `blockBlowupMap univ p = blowupMap p` — the full-ambient map is the `S = univ` instance. -/
theorem blockBlowupMap_univ (p : Fin D) :
    blockBlowupMap (Finset.univ) p = blowupMap p := by
  funext w j
  simp only [blockBlowupMap, blowupMap, Finset.mem_univ, if_true]

/-- The Jacobian `ContinuousLinearMap` of `blockBlowupMap S p` at `w`. -/
noncomputable def blockBlowupDeriv (S : Finset (Fin D)) (p : Fin D) (w : Fin D → ℝ) :
    (Fin D → ℝ) →L[ℝ] (Fin D → ℝ) :=
  ContinuousLinearMap.pi (fun j ↦
    if j = p then ContinuousLinearMap.proj p
    else if j ∈ S then (w p) • ContinuousLinearMap.proj j + (w j) • ContinuousLinearMap.proj p
    else ContinuousLinearMap.proj j)

theorem hasFDerivAt_blockBlowupMap (S : Finset (Fin D)) (p : Fin D) (w : Fin D → ℝ) :
    HasFDerivAt (blockBlowupMap S p) (blockBlowupDeriv S p w) w := by
  rw [blockBlowupDeriv, hasFDerivAt_pi]
  intro j
  by_cases hj : j = p
  · have hf : (fun w : Fin D → ℝ ↦ blockBlowupMap S p w j) = fun w ↦ w p := by
      funext w; simp [blockBlowupMap, hj]
    rw [hf, if_pos hj]; exact hasFDerivAt_apply p w
  · by_cases hjS : j ∈ S
    · have hf : (fun w : Fin D → ℝ ↦ blockBlowupMap S p w j) = fun w ↦ w p * w j := by
        funext w; simp [blockBlowupMap, hj, hjS]
      rw [hf, if_neg hj, if_pos hjS]
      exact (hasFDerivAt_apply p w).mul (hasFDerivAt_apply j w)
    · have hf : (fun w : Fin D → ℝ ↦ blockBlowupMap S p w j) = fun w ↦ w j := by
        funext w; simp [blockBlowupMap, hj, hjS]
      rw [hf, if_neg hj, if_neg hjS]; exact hasFDerivAt_apply j w

/-- The entries of the Jacobian matrix of `blockBlowupMap S p` at `w`. -/
theorem toMatrix'_blockBlowupDeriv (S : Finset (Fin D)) (p : Fin D) (w : Fin D → ℝ) (a c : Fin D) :
    LinearMap.toMatrix' (blockBlowupDeriv S p w).toLinearMap a c =
      if a = p then (if p = c then 1 else 0)
      else if a ∈ S then (w p * (if a = c then 1 else 0) + w a * (if p = c then 1 else 0))
      else (if a = c then 1 else 0) := by
  rw [LinearMap.toMatrix'_apply]
  by_cases ha : a = p
  · subst ha; simp [blockBlowupDeriv, Pi.single_apply]
  · by_cases haS : a ∈ S
    · simp [blockBlowupDeriv, Pi.single_apply, ha, haS]
    · simp [blockBlowupDeriv, Pi.single_apply, ha, haS]

/-- **O9 (seat-w0l3) — the block-center Jacobian determinant** `jacDet (blockBlowupMap S p) w =
(w p)^(|S|−1)`, `|S|`-general (including `|S| = 1`, giving `w_p^0 = 1`). Same `BlockTriangular.det`
pattern as `jacDet_blowupMap`: the pivot row is its own `1`-block, the `|S|−1` non-pivot center rows
are `w_p·I`, the spectator rows are `I`. Center-size−1 exponent (W2), never ambient−1. -/
theorem jacDet_blockBlowupMap {S : Finset (Fin D)} {p : Fin D} (hp : p ∈ S) (w : Fin D → ℝ) :
    jacDet (blockBlowupMap S p) w = (w p) ^ (S.card - 1) := by
  unfold jacDet
  rw [(hasFDerivAt_blockBlowupMap S p w).fderiv,
    ← LinearMap.det_toMatrix' (blockBlowupDeriv S p w).toLinearMap]
  set M := LinearMap.toMatrix' (blockBlowupDeriv S p w).toLinearMap with hMdef
  -- The pivot row is clean off its diagonal ⇒ two-block-triangular at the `(· ≠ p)` predicate
  -- (both `≠ p` and `¬ · ≠ p` use the generic `Subtype.fintype`, avoiding a `Fintype.subtypeEq` clash).
  have htri : ∀ i, ¬ i ≠ p → ∀ j, j ≠ p → M i j = 0 := by
    intro i hi j hj
    obtain rfl : i = p := not_not.mp hi
    rw [hMdef, toMatrix'_blockBlowupDeriv, if_pos rfl, if_neg (fun h ↦ hj h.symm)]
  rw [M.twoBlockTriangular_det (· ≠ p) htri]
  -- The non-pivot block `{a ≠ p}` is diagonal `(if a ∈ S then w_p else 1)`, det `= w_p ^ (|S|−1)`.
  have hb0 : (M.toSquareBlockProp (· ≠ p)).det = (w p) ^ (S.card - 1) := by
    have hdiag : M.toSquareBlockProp (· ≠ p)
        = Matrix.diagonal (fun i : {a // a ≠ p} ↦ if (↑i : Fin D) ∈ S then w p else 1) := by
      ext a b
      have ha : (↑a : Fin D) ≠ p := a.2
      have hb : (↑b : Fin D) ≠ p := b.2
      rw [Matrix.toSquareBlockProp_def, Matrix.of_apply, hMdef, toMatrix'_blockBlowupDeriv,
        if_neg ha, if_neg (fun h : p = (↑b : Fin D) ↦ hb h.symm), Matrix.diagonal_apply]
      by_cases hab : a = b
      · subst hab
        by_cases haS : (↑a : Fin D) ∈ S <;> simp [haS]
      · have hab' : (↑a : Fin D) ≠ ↑b := fun h ↦ hab (Subtype.ext h)
        by_cases haS : (↑a : Fin D) ∈ S <;> simp [haS, hab, hab']
    rw [hdiag, Matrix.det_diagonal,
      ← Finset.prod_subtype (Finset.univ.filter (fun a ↦ a ≠ p)) (fun x ↦ by simp)
        (fun a ↦ if a ∈ S then w p else 1),
      Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    congr 1
    rw [show (Finset.univ.filter (fun a ↦ a ≠ p)).filter (fun a ↦ a ∈ S) = S.erase p from ?_,
      Finset.card_erase_of_mem hp]
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  -- The pivot block `{a // ¬ a ≠ p}` is the identity (`M p p = 1`); its det is `1`.
  rw [hb0, show M.toSquareBlockProp (fun i ↦ ¬ i ≠ p) = 1 from ?_, Matrix.det_one, mul_one]
  ext a b
  have haa : (↑a : Fin D) = p := not_not.mp a.2
  have hbb : (↑b : Fin D) = p := not_not.mp b.2
  have hab : a = b := Subtype.ext (haa.trans hbb.symm)
  rw [Matrix.toSquareBlockProp_def, Matrix.of_apply, hMdef, toMatrix'_blockBlowupDeriv,
    haa, hbb, if_pos rfl, if_pos rfl, hab, Matrix.one_apply_eq]

/-- **The origin blow-up Jacobian, UNCONDITIONALLY** `jacDet (blowupMap i) w = (w i)^(D-1)` for ALL
`D` — the `S = univ` instance of `jacDet_blockBlowupMap` (via `blockBlowupMap_univ`,
`Finset.card_univ`, `Fintype.card_fin`). This SUBSUMES `OriginBlowup.jacDet_blowupMap`, whose
`2 ≤ D` hypothesis is REDUNDANT: the block-center determinant is unconditional, and
`univ.card - 1 = D - 1` gives the correct `(w i)^0 = 1` at `D = 1` (the trivial `d ↦ u` step).
The `OriginBlowup` form is kept (self-consumed there + an `AxCheck` root); use this one when the
`2 ≤ D` bound is unavailable. -/
theorem jacDet_blowupMap_unconditional (i : Fin D) (w : Fin D → ℝ) :
    jacDet (blowupMap i) w = (w i) ^ (D - 1) := by
  rw [← blockBlowupMap_univ i, jacDet_blockBlowupMap (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin]

/-- **O9 (seat-w0l3) — block-center a.e.-injectivity** off the pivot hyperplane `{w_p = 0}`. -/
theorem injOn_blockBlowupMap {S : Finset (Fin D)} {p : Fin D} (hp : p ∈ S) :
    Set.InjOn (blockBlowupMap S p) (Set.univ \ {w : Fin D → ℝ | w p = 0}) := by
  intro w hw w' _ heq
  have hwp : w p ≠ 0 := by simpa using hw.2
  have hpp : w p = w' p := by
    have := congrFun heq p; simpa [blockBlowupMap] using this
  funext j
  by_cases hj : j = p
  · rw [hj]; exact hpp
  · by_cases hjS : j ∈ S
    · have hprod : w p * w j = w' p * w' j := by
        have := congrFun heq j; simpa [blockBlowupMap, hj, hjS] using this
      rw [hpp] at hprod
      exact mul_left_cancel₀ (hpp ▸ hwp) hprod
    · have := congrFun heq j; simpa [blockBlowupMap, hj, hjS] using this

end DLNFibre.Core.Aoyagi
