import DLNFibre.DLN.Aoyagi.Corank2Chart334
import DLNFibre.DLN.Aoyagi.Corank2ChartJac
import DLNFibre.DLN.Aoyagi.Corank2FanDef334
import DLNFibre.DLN.Aoyagi.LeafCoverTiling

/-!
# `DLN.Aoyagi.Corank2FanCover334` — #112 rung 5d part-2: the (3,3,4) fan COVER

The SOLE remaining obligation for the full (3,3,4) Resolution: the ball-cover
`ball 0 ρ ⊆ ⋃ c, (charts c).g '' (charts c).dom` that `Corank2Chart334.resolution334_of_ballCover`
consumes. Built on the `LeafCoverTiling` fan engine + the box-containment of the faithful shear.

## §0 — the substantive box-containment: `shearH` inflates by `r + 2r²`

The faithful shear `shearH` (`Corank2GWrapDecomp`) is `blockShear shearPhiH` (`Corank2ChartJac.shearH_eq`).
Its displacement has slots 4–7 with ONE product (`|·| ≤ r²`) and slots 8–11 with TWO products
(`|·| ≤ 2r²`), so the sup-norm bound is `2r²` — NOT the one-product `r²` of `outerShear`. Hence the box
inflation is `f = r ↦ r + 2r²` (the general `blockShear_covers_scaled` below generalizes
`GeneralGeoAtlas.blockShear_covers_of_norm_bound`'s `C = 1` to `C = 2`). This is the "faithful-shear
box-containment at Fin-21" the fan cover consumes.
-/

open MeasureTheory Set Metric
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.Corank2GWrapDecomp
open DLNFibre.DLN.Aoyagi.Corank2ChartJac
open DLNFibre.DLN.Aoyagi.GeneralGeoAtlas
open DLNFibre.DLN.Aoyagi.LeafCoverTiling DLNFibre.DLN.Aoyagi.LeafCoverTiling.FanTree

namespace DLNFibre.DLN.Aoyagi.Corank2FanCover334

/-- **The scaled box-containment atom** — `GeneralGeoAtlas.blockShear_covers_of_norm_bound` with the
quadratic constant `C` explicit (`‖φ x‖ ≤ C·r²` ⟹ inflation `r + C·r²`). Reusable engine material:
a rank-`q` block-shear step (each corrected coordinate a sum of `q` products) has `C = q`. -/
theorem blockShear_covers_scaled {D : ℕ} {φ : (Fin D → ℝ) → (Fin D → ℝ)} (keep : Fin D → Prop)
    (hkeep : ∀ u i, keep i → φ u i = 0)
    (hread : ∀ u v : Fin D → ℝ, (∀ i, keep i → u i = v i) → φ u = φ v)
    {r C : ℝ} (hquad : ∀ x : Fin D → ℝ, ‖x‖ ≤ r → ‖φ x‖ ≤ C * r ^ 2) :
    closedBall (0 : Fin D → ℝ) r ⊆ blockShear φ '' closedBall 0 (r + C * r ^ 2) := by
  intro x hx
  have hxr : ‖x‖ ≤ r := mem_closedBall_zero_iff.mp hx
  refine ⟨blockShearInv φ x, ?_, blockShearInv_rightInverse φ keep hkeep hread x⟩
  rw [mem_closedBall_zero_iff]
  calc ‖blockShearInv φ x‖ = ‖x - φ x‖ := rfl
    _ ≤ ‖x‖ + ‖φ x‖ := norm_sub_le _ _
    _ ≤ r + C * r ^ 2 := add_le_add hxr (hquad x hxr)

/-- **The `shearPhiH` sup-norm bound `2r²`.** Slots 4–7 are one product (`≤ r²`), slots 8–11 are two
products (`≤ 2r²`), the rest `0`; so `‖shearPhiH x‖ ≤ 2‖x‖²` at radius `r`. -/
theorem shearPhiH_norm_bound {x : Fin 21 → ℝ} {r : ℝ} (hx : ‖x‖ ≤ r) :
    ‖shearPhiH x‖ ≤ 2 * r ^ 2 := by
  have hr : 0 ≤ r := le_trans (norm_nonneg x) hx
  have habs : ∀ i : Fin 21, |x i| ≤ r := fun i ↦ by
    rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm x i).trans hx
  have key : ∀ a b : Fin 21, |x a * x b| ≤ r ^ 2 := fun a b ↦ by
    rw [abs_mul, sq]; exact mul_le_mul (habs a) (habs b) (abs_nonneg _) hr
  -- helper for the two-product slots: `|-(x a·x b) - x c·x d| ≤ 2r²`
  have two : ∀ a b c d : Fin 21, |(-(x a * x b)) - x c * x d| ≤ 2 * r ^ 2 := fun a b c d ↦ by
    rw [abs_le]
    obtain ⟨hab1, hab2⟩ := abs_le.mp (key a b)
    obtain ⟨hcd1, hcd2⟩ := abs_le.mp (key c d)
    constructor <;> linarith
  -- helper for the one-product slots: `|x a·x b| ≤ 2r²`
  have one : ∀ a b : Fin 21, |x a * x b| ≤ 2 * r ^ 2 := fun a b ↦
    le_trans (key a b) (by linarith [sq_nonneg r])
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i <;>
    simp only [shearPhiH, Fin.reduceFinMk, Fin.reduceEq, if_true, if_false, abs_zero] <;>
    try positivity
  · exact one 0 2   -- slot 4
  · exact one 1 2   -- slot 5
  · exact one 0 3   -- slot 6
  · exact one 1 3   -- slot 7
  · exact two 0 12 1 16   -- slot 8
  · exact two 0 13 1 17   -- slot 9
  · exact two 0 14 1 18   -- slot 10
  · exact two 0 15 1 19   -- slot 11

/-- **THE FAITHFUL-SHEAR BOX-CONTAINMENT (Fin-21).** `closedBall 0 r ⊆ shearH '' closedBall 0 (r + 2r²)`
— `shearH = blockShear shearPhiH` (`shearH_eq`) fed to `blockShear_covers_scaled` at `C = 2`. This is
the substantive per-node shear clause the (3,3,4) fan's `Covers (r ↦ r + 2r²) gWrapFan` consumes. -/
theorem shearH_covers {r : ℝ} :
    closedBall (0 : Fin 21 → ℝ) r ⊆ shearH '' closedBall 0 (r + 2 * r ^ 2) := by
  rw [shearH_eq]
  exact blockShear_covers_scaled shearKeepH (fun u i hi ↦ shearPhiH_keep u i hi)
    (fun u v h ↦ shearPhiH_read u v h) (fun x hx ↦ shearPhiH_norm_bound hx)

/-! ## §1 — the permutation is a sup-norm isometry; the composite `shearH ∘ permP` box-containment -/

/-- **`permP` is a sup-norm isometry, so its image of a `0`-ball contains that ball** (`permP` is a
coordinate reindex by `permSigma`, bijective; `y := x ∘ permSigma.symm` has `‖y‖ ≤ ‖x‖ ≤ s` and
`permP y = x`). -/
theorem permP_image_superset {s : ℝ} :
    closedBall (0 : Fin 21 → ℝ) s ⊆ permP '' closedBall 0 s := by
  intro x hx
  refine ⟨fun j ↦ x (permSigma.symm j), ?_, ?_⟩
  · have hs : 0 ≤ s := le_trans (norm_nonneg x) (mem_closedBall_zero_iff.mp hx)
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hs]
    intro j
    exact (norm_le_pi_norm x (permSigma.symm j)).trans (mem_closedBall_zero_iff.mp hx)
  · funext i
    show x (permSigma.symm (permIdx i)) = x i
    rw [show permIdx i = permSigma i from rfl, Equiv.symm_apply_apply]

/-- **The composite `shearH ∘ permP` box-containment** — `closedBall 0 t ⊆ (shearH ∘ permP) ''
closedBall 0 (t + 2t²)`: `permP` fixes the `0`-ball (isometry), then `shearH_covers`. This is the
box-containment for gWrap's outer fan-node shear `σ = shearH ∘ permP`. -/
theorem shearHpermP_covers {t : ℝ} :
    closedBall (0 : Fin 21 → ℝ) t ⊆ (shearH ∘ permP) '' closedBall 0 (t + 2 * t ^ 2) := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := shearH_covers (r := t) hx
  obtain ⟨z, hz, hzy⟩ := permP_image_superset hy
  exact ⟨z, hz, by rw [Function.comp_apply, hzy]; exact hyx⟩

/-! ## §2 — the cover of the SHARED `gWrapFan` (`Corank2FanDef334`, imported to avoid divergence)

`gWrapFan`/`gWrapFanSteps` are routeP-p1's shared defs (`DLNFibre.DLN.Aoyagi.gWrapFan`), so this cover
and the crux-B transport charts (#143) tile the SAME fan. -/

/-- **The per-step box-containment** for `gWrapFanSteps` (the `covers_fanOfSteps` hypothesis): the
outer node's `shearH ∘ permP` via `shearHpermP_covers`; the two id nodes trivially (`t ≤ t + 2t²`). -/
theorem gWrapFanSteps_boxContain :
    ∀ s ∈ gWrapFanSteps, ∀ p ∈ s.center, ∀ t : ℝ,
      closedBall (0 : Fin 21 → ℝ) t ⊆ s.shear p '' closedBall 0 ((fun r ↦ r + 2 * r ^ 2) t) := by
  intro s hs
  simp only [gWrapFanSteps] at hs
  fin_cases hs <;> intro p _ t
  · exact shearHpermP_covers
  · rw [Set.image_id]
    refine closedBall_subset_closedBall ?_
    show t ≤ t + 2 * t ^ 2
    nlinarith [sq_nonneg t]
  · rw [Set.image_id]
    refine closedBall_subset_closedBall ?_
    show t ≤ t + 2 * t ^ 2
    nlinarith [sq_nonneg t]

/-- **`Covers` for the shared `gWrapFan 1`** (the fan-fold cover condition at target radius `1`), from
the per-step box-containments via `covers_fanOfSteps`. -/
theorem gWrapFan_covers : Covers (fun r ↦ r + 2 * r ^ 2) (gWrapFan 1) 1 :=
  covers_fanOfSteps gWrapFanSteps 1 gWrapFanSteps_boxContain

/-- **THE (3,3,4) BALL-COVER (`-- map: #112-5d-cover`).** `∃ ρ > 0, ball 0 ρ ⊆ (gWrapFan 1).leafImages`
— a punctured neighbourhood of `0` is covered by the fan's leaf-chart images (the pivot-paths of
`gWrap`'s three blow-ups). Feeds `resolution334_of_ballCover` once the leaf composites are enumerated as
the `charts` family (crux B / #143). Via `covers_subset` on `gWrapFan_covers`. -/
theorem exists_ball_subset_gWrapFan_leafImages :
    ∃ ρ : ℝ, 0 < ρ ∧ ball (0 : Fin 21 → ℝ) ρ ⊆ (gWrapFan 1).leafImages :=
  exists_ball_subset_leafImages (gWrapFan 1) gWrapFan_covers

end DLNFibre.DLN.Aoyagi.Corank2FanCover334
