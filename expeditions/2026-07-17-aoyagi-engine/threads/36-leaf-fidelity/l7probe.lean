import DLNFibre.DLN.Aoyagi.MonumentAtlas
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine
open scoped Topology
open Set Metric

/- (b) L7/L8 `∀ atlas` soundness test. Build a DEGENERATE but well-formed GeoAtlasData
   (one chart, NO steps ⟹ gmap = id, dom = {0}) and show L7's cover conclusion is FALSE for it.
   This refutes `leafPath_compactCover`'s statement (∀ atlas, ∃ρ>0, ball ⊆ ⋃ gmap''dom). -/
example {N : ℕ} (d : Fin (N + 1) → ℕ) (e : (Fin (DLNFibre.DLN.Aoyagi.flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (hfd : 0 < DLNFibre.DLN.Aoyagi.flatDim d)
    (hL7 : ∀ atlas : GeoAtlasData d e,
      ∃ ρ : ℝ, 0 < ρ ∧
        Metric.ball (0 : Fin (DLNFibre.DLN.Aoyagi.flatDim d) → ℝ) ρ ⊆ ⋃ c, (atlas.gmap c) '' (atlas.dom c)) :
    False := by
  set i0 : Fin (DLNFibre.DLN.Aoyagi.flatDim d) := ⟨0, hfd⟩ with hi0
  let atlas : GeoAtlasData d e :=
    { n := 1
      hn := one_pos
      steps := fun _ => []
      dom := fun _ => {0}
      region := fun _ => Set.univ
      bexp := fun _ => (fun j => if j = i0 then 1 else 0)
      jac := fun _ => (fun _ => 0)
      hregion_open := fun _ => isOpen_univ
      hzero_region := fun _ => Set.mem_univ _
      hdom_compact := fun _ => isCompact_singleton
      hzero_dom := fun _ => rfl
      hdom_sub := fun _ => Set.subset_univ _
      hbind := fun _ => ⟨i0, by simp [bindingAxes]⟩
      hsqfree := fun _ a ha => by
        simp only [bindingAxes, Finset.mem_filter] at ha
        by_cases h : a = i0
        · simp [h]
        · simp [h] at ha }
  obtain ⟨ρ, hρ, hsub⟩ := hL7 atlas
  -- gmap c = id, dom c = {0}, so ⋃ c, gmap c '' dom c = {0}; but ball 0 ρ has a nonzero point.
  have hgmap : ∀ c, atlas.gmap c '' atlas.dom c = ({0} : Set (Fin (DLNFibre.DLN.Aoyagi.flatDim d) → ℝ)) := by
    intro c
    rw [show atlas.gmap c = id from rfl, Set.image_id]
  set w : Fin (DLNFibre.DLN.Aoyagi.flatDim d) → ℝ := fun _ => ρ / 2 with hw
  have hwball : w ∈ Metric.ball (0 : Fin (DLNFibre.DLN.Aoyagi.flatDim d) → ℝ) ρ := by
    rw [Metric.mem_ball, dist_pi_lt_iff hρ]
    intro i
    simp only [hw, Pi.zero_apply, Real.dist_eq, sub_zero, abs_of_pos (by linarith : (0:ℝ) < ρ/2)]
    linarith
  have hwmem := hsub hwball
  rw [Set.mem_iUnion] at hwmem
  obtain ⟨c, hc⟩ := hwmem
  rw [hgmap c, Set.mem_singleton_iff] at hc
  have : w i0 = (0 : Fin (DLNFibre.DLN.Aoyagi.flatDim d) → ℝ) i0 := by rw [hc]
  simp only [hw, Pi.zero_apply] at this
  linarith
