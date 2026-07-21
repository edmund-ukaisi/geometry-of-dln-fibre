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

/-- **O9 (seat-w0l3) — the block-center Jacobian determinant** `jacDet (blockBlowupMap S p) w =
(w p)^(|S|−1)`, `|S|`-general (including `|S| = 1`, giving `w_p^0 = 1`). Same `BlockTriangular.det`
pattern as `jacDet_blowupMap`: the pivot row is its own `1`-block, the `|S|−1` non-pivot center rows
are `w_p·I`, the spectator rows are `I`. Center-size−1 exponent (W2), never ambient−1. -/
@[blueprint]
theorem jacDet_blockBlowupMap {S : Finset (Fin D)} {p : Fin D} (hp : p ∈ S) (w : Fin D → ℝ) :
    jacDet (blockBlowupMap S p) w = (w p) ^ (S.card - 1) := by
  -- map: B-O9-blockBlowup-jacDet (BlockTriangular.det, center-size−1 exponent)
  sorry

/-- **O9 (seat-w0l3) — block-center a.e.-injectivity** off the pivot hyperplane `{w_p = 0}`. -/
@[blueprint]
theorem injOn_blockBlowupMap {S : Finset (Fin D)} {p : Fin D} (hp : p ∈ S) :
    Set.InjOn (blockBlowupMap S p) (Set.univ \ {w : Fin D → ℝ | w p = 0}) := by
  -- map: B-O9-blockBlowup-injOn (invert off the pivot hyperplane; spectators carry through)
  sorry

end DLNFibre.Core.Aoyagi
