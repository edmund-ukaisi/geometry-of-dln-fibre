import DLNFibre.Core.Aoyagi.BlockBlowup

/-!
# `Core.Aoyagi.BlockBlowupCover` — the pivot-fanned block-blow-up cover atom (Q)

The block-center generalization of `OriginBlowup.ball_subset_iUnion_blowup_image` (the `S = univ`
origin blow-up cover) to a **center-`S` block blow-up × spectator passthrough**: the open unit cube
around `0` is covered by the union, over pivots `p ∈ S`, of the images of the `S`-center blow-up
charts with pivot `p`, the off-`S` (spectator) coordinates passed through.

This is the per-step cover atom the monument's cover fold (L7 salvage option (b)) consumes; the
atom is SHEAR-FREE (a pure block blow-up cover). The routing is the argmax-over-`S`: at a target
`x`, pick the center pivot `p` maximising `|x_p|` and lift `w_p = x_p`, `w_q = x_q / x_p`
(`q ∈ S \ {p}`), spectators `w_j = x_j` — the `S`-ratios are `≤ 1` by maximality, spectators
unchanged. This is the block-atom `(Q)` of the L7 `fan-design-certificate.md` §2.1.

`S = univ` recovers `OriginBlowup.ball_subset_iUnion_blowup_image` (no spectators, argmax over
all of `Fin D`); this file does not re-derive that — it stands on the same `Core.Aoyagi` atoms.
-/

open MeasureTheory Set Filter Topology RLCT

namespace DLNFibre.Core.Aoyagi

variable {D : ℕ}

/-- **The pivot-fanned block-blow-up cover (Q)**: the open unit cube around `0` is covered by the
images of the `|S|` block-blow-up charts of the center `S`, one per pivot `p ∈ S`, over the closed
unit cube source box; spectator coordinates (`∉ S`) are passed through. The routing is
`p = argmax_{q ∈ S} |x_q|`, `w_p = x_p`, `w_q = x_q / x_p`, spectators `w_j = x_j`. -/
theorem ball_subset_iUnion_blockBlowup_image {S : Finset (Fin D)} (hS : S.Nonempty) :
    Metric.ball (0 : Fin D → ℝ) 1 ⊆
      ⋃ p ∈ S, (blockBlowupMap S p) '' (Metric.closedBall 0 1) := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff one_pos] at hx
  -- the pivot is the center coordinate of maximal absolute value
  obtain ⟨p, hpS, hp⟩ := Finset.exists_max_image S (fun j ↦ |x j|) hS
  have hxp1 : |x p| ≤ 1 := by have h := hx p; rw [Real.norm_eq_abs] at h; exact h.le
  rw [Set.mem_iUnion₂]
  refine ⟨p, hpS, ?_⟩
  by_cases hxp : x p = 0
  · -- max over `S` is `0` ⟹ every center coordinate is `0`; spectators pass through unchanged
    have hxj0 : ∀ q ∈ S, x q = 0 := fun q hq ↦ by
      have := hp q hq; rw [hxp, abs_zero] at this; exact abs_nonpos_iff.mp this
    refine ⟨fun j ↦ if j ∈ S then 0 else x j, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)]
      intro j
      rw [Real.norm_eq_abs]
      by_cases hjS : j ∈ S
      · simp [hjS]
      · simp only [if_neg hjS]; have h := hx j; rw [Real.norm_eq_abs] at h; exact h.le
    · funext j
      by_cases hj : j = p
      · subst hj; simp [blockBlowupMap, hpS, hxp]
      · by_cases hjS : j ∈ S
        · simp only [blockBlowupMap, if_neg hj, if_pos hjS, if_pos hpS, mul_zero]
          exact (hxj0 j hjS).symm
        · simp [blockBlowupMap, hj, hjS]
  · -- max over `S` is nonzero: the standard argmax lift, ratios `≤ 1` by maximality
    refine ⟨fun j ↦ if j = p then x p else if j ∈ S then x j / x p else x j, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)]
      intro j
      rw [Real.norm_eq_abs]
      by_cases hj : j = p
      · rw [hj]; simpa using hxp1
      · by_cases hjS : j ∈ S
        · simp only [if_neg hj, if_pos hjS, abs_div]
          rw [div_le_one (abs_pos.mpr hxp)]; exact hp j hjS
        · simp only [if_neg hj, if_neg hjS]
          have h := hx j; rw [Real.norm_eq_abs] at h; exact h.le
    · funext j
      by_cases hj : j = p
      · subst hj; simp [blockBlowupMap]
      · by_cases hjS : j ∈ S
        · simp [blockBlowupMap, hj, hjS, mul_div_cancel₀, hxp]
        · simp [blockBlowupMap, hj, hjS]

end DLNFibre.Core.Aoyagi
