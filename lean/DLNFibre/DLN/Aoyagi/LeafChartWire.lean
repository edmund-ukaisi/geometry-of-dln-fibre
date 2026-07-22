import DLNFibre.DLN.Aoyagi.MonumentAtlas

/-!
# `DLN.Aoyagi.LeafChartWire` — L6 standalone leaf proof (SEAT-L6, fresh lane)

The chart-geometry leaf (L6) of the monument, proved standalone (statement-identical to
`MonumentAtlas.leafPath_chartGeometry`, primed to avoid the import clash — arch-C swaps the leaf
sorry to `:= …'` at integration). L6 assembles a certified `Chart (coreGen d e) 0` from a
fold-produced atlas chart `c`: the path map `gmap c = pathMap (steps.map σ)` is analytic,
origin-fixing, a.e.-injective, and (the ideal fields) carries the two `RegionRepresents`
inclusions directly from the L1 hypotheses (`hfwd`/`hbwd`), which pin `M' = 1`
(`monoOf = monomialFam` at width 1).

The a.e.-injectivity fold is `injOn_pathMap_off_critical`: `pathMap σs` is injective off its own
critical set `{jacDet (pathMap σs) = 0}`, folded from the per-step `GeoStep.hσ_inj` via
`injOn_comp_diff` + the `jacDet_comp` chain rule (a per-step exceptional locus `{jacWeight jexp = 0}`
equals `{jacDet σ = 0}` by `hσ_jac`).
-/

open MeasureTheory Set Filter Topology RLCT
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi

variable {N : ℕ}

/-! ## The a.e.-injectivity fold: `pathMap` is injective off its critical set -/

/-- **The path map is injective off its own critical set.** Folding `injOn_comp_diff` down the list:
each step `σ` is injective off `{jacDet σ = 0}`, and by the `jacDet_comp` chain rule the composite's
non-injective locus lands inside `{jacDet (pathMap σs) = 0}`. The measure-free half of L6's
a.e.-injectivity (the caller supplies nullity of the critical set). -/
theorem injOn_pathMap_off_critical {D : ℕ} (σs : List ((Fin D → ℝ) → (Fin D → ℝ)))
    (hdiff : ∀ σ ∈ σs, Differentiable ℝ σ)
    (hinj : ∀ σ ∈ σs, Set.InjOn σ (Set.univ \ {w | jacDet σ w = 0})) :
    Set.InjOn (pathMap σs) (Set.univ \ {u | jacDet (pathMap σs) u = 0}) := by
  induction σs with
  | nil =>
    simp only [pathMap_nil]
    exact Set.injOn_id _
  | cons σ rest ih =>
    have hσdiff : Differentiable ℝ σ := hdiff σ (List.mem_cons.mpr (Or.inl rfl))
    have hrestdiff : ∀ τ ∈ rest, Differentiable ℝ τ :=
      fun τ hτ ↦ hdiff τ (List.mem_cons.mpr (Or.inr hτ))
    have hσinj : Set.InjOn σ (Set.univ \ {w | jacDet σ w = 0}) :=
      hinj σ (List.mem_cons.mpr (Or.inl rfl))
    have hrestinj : ∀ τ ∈ rest, Set.InjOn τ (Set.univ \ {w | jacDet τ w = 0}) :=
      fun τ hτ ↦ hinj τ (List.mem_cons.mpr (Or.inr hτ))
    have ihr := ih hrestdiff hrestinj
    have hcomp := injOn_comp_diff hσinj ihr
    rw [pathMap_cons]
    refine hcomp.mono ?_
    refine Set.diff_subset_diff_right ?_
    intro u hu
    have hchain : jacDet (σ ∘ pathMap rest) u
        = jacDet σ (pathMap rest u) * jacDet (pathMap rest) u :=
      jacDet_comp u (hσdiff (pathMap rest u)) (differentiable_pathMap rest hrestdiff u)
    rcases hu with h | h
    · -- u in {jacDet (pathMap rest) = 0}
      have h0 : jacDet (pathMap rest) u = 0 := h
      exact Set.mem_setOf_eq ▸ (by rw [hchain, h0, mul_zero])
    · -- u in (pathMap rest)⁻¹' {jacDet σ = 0}
      have h0 : jacDet σ (pathMap rest u) = 0 := h
      exact Set.mem_setOf_eq ▸ (by rw [hchain, h0, zero_mul])

/-! ## Continuity of the flattened core generators (for `Chart.hFmeas`) -/

/-- Each flattened core generator `coreGen d e i` is continuous (`e` continuous, `mult` continuous,
entry-evaluation continuous), hence measurable. -/
theorem continuous_coreGen (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (i : Fin (d (Fin.last N) * d 0)) :
    Continuous (coreGen d e i) := by
  unfold coreGen
  exact (continuous_apply _).comp
    ((continuous_apply _).comp ((continuous_mult d).comp e.continuous))

/-! ## L6 — the chart geometry -/

/-- **L6 — the chart geometry** (statement-identical to `MonumentAtlas.leafPath_chartGeometry`;
primed). Assembles a certified `Chart (coreGen d e) 0` from a fold-produced atlas chart. -/
theorem leafPath_chartGeometry' (d : Fin (N + 1) → ℕ) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (atlas : GeoAtlasData d e) (c : Fin atlas.n) (hfold : FoldProduced d e atlas)
    (hfwd : RegionRepresents (fun i ↦ coreGen d e i ∘ atlas.gmap c)
      (fun _ : Fin 1 ↦ monoOf (atlas.bexp c)) (atlas.region c))
    (hbwd : RegionRepresents (fun _ : Fin 1 ↦ monoOf (atlas.bexp c))
      (fun i ↦ coreGen d e i ∘ atlas.gmap c) (atlas.region c)) :
    ∃ chart : Chart (coreGen d e) 0,
      chart.g = atlas.gmap c ∧ chart.dom = atlas.dom c ∧ chart.nbhd = atlas.region c ∧
        chart.bexp chart.k₀ = atlas.bexp c ∧ chart.jac = atlas.jac c := by
  obtain ⟨leafOf, hmem, hsurj, hjac_mem, hjac_onto, hdom_ball, hstep, hjac_tie, hcard⟩ := hfold
  -- The step-map list and its per-step certificates.
  set σs := (atlas.steps c).map GeoStep.σ with hσs
  have hgmap : atlas.gmap c = pathMap σs := rfl
  have hstep_zero : ∀ σ ∈ σs, σ 0 = 0 := by
    intro σ hσ; rw [hσs, List.mem_map] at hσ; obtain ⟨s, _, rfl⟩ := hσ; exact s.hσ0
  have hstep_an : ∀ σ ∈ σs, AnalyticOnNhd ℝ σ Set.univ := by
    intro σ hσ; rw [hσs, List.mem_map] at hσ; obtain ⟨s, _, rfl⟩ := hσ; exact s.hσ_an
  have hstep_diff : ∀ σ ∈ σs, Differentiable ℝ σ := by
    intro σ hσ; exact differentiableOn_univ.mp (hstep_an σ hσ).differentiableOn
  have hstep_inj : ∀ σ ∈ σs, Set.InjOn σ (Set.univ \ {w | jacDet σ w = 0}) := by
    intro σ hσ; rw [hσs, List.mem_map] at hσ; obtain ⟨s, _, rfl⟩ := hσ
    have hset : {w : Fin (flatDim d) → ℝ | jacDet s.σ w = 0} = {w | jacWeight s.jexp w = 0} := by
      ext w; simp only [Set.mem_setOf_eq]; rw [← abs_eq_zero, s.hσ_jac w]
    rw [hset]; exact s.hσ_inj
  -- Analyticity / continuity / origin-fixing of the composed path map.
  have hg_an : AnalyticOnNhd ℝ (atlas.gmap c) Set.univ := by
    rw [hgmap]; exact analyticOnNhd_pathMap σs hstep_an
  have hg_cont : Continuous (atlas.gmap c) :=
    continuousOn_univ.mp hg_an.continuousOn
  have hg_zero : atlas.gmap c 0 = 0 := by rw [hgmap]; exact pathMap_zero σs hstep_zero
  -- a.e.-injectivity off the critical set.
  have hinj : Set.InjOn (atlas.gmap c)
      (Set.univ \ {u | jacDet (atlas.gmap c) u = 0}) := by
    rw [hgmap]; exact injOn_pathMap_off_critical σs hstep_diff hstep_inj
  refine ⟨{
    g := atlas.gmap c
    hg0 := hg_zero
    hg_cont := hg_cont
    hg_analytic := hg_an
    hFmeas := fun i ↦ (continuous_coreGen d e i).measurable
    dom := atlas.dom c
    hdom_compact := atlas.hdom_compact c
    hdom_zero := atlas.hzero_dom c
    nbhd := atlas.region c
    hnbhd_open := atlas.hregion_open c
    hdom_sub := atlas.hdom_sub c
    excep := {u | jacDet (atlas.gmap c) u = 0}
    hexcep_meas := ?_
    hexcep_null := ?_
    hg_inj := hinj.mono (Set.diff_subset_diff_left (Set.subset_univ _))
    M' := 1
    bexp := fun _ : Fin 1 ↦ atlas.bexp c
    k₀ := 0
    hchain := fun _ _ ↦ le_refl _
    hbind := atlas.hbind c
    hunit_mult := atlas.hsqfree c
    jac := atlas.jac c
    unit := fun _ ↦ 1
    hunit_cont := continuousOn_const
    hunit_ne := fun _ _ ↦ one_ne_zero
    hjac := ?_
    hideal_fwd := hfwd
    hideal_bwd := hbwd }, rfl, rfl, rfl, rfl, rfl⟩
  · -- hexcep_meas : {jacDet (gmap c) = 0} measurable — LIVE-frontier (REAL LABOUR #1, nullity leg).
    sorry
  · -- hexcep_null : volume {jacDet (gmap c) = 0} = 0 — LIVE-frontier (REAL LABOUR #1, nullity leg).
    sorry
  · -- hjac : |jacDet (gmap c) u| = jacWeight (jac c) u * |1| on region c — REAL LABOUR #2.
    -- SUSPECT (PM-P1): the collapse to jacWeight (∑ jexp) with unit ≡ 1 holds iff each step's pivot
    -- coordinate is preserved by all deeper steps; that alignment is NOT among FoldProduced's
    -- (numeric) clauses. Escalated to team-lead.
    sorry

end DLNFibre.DLN.Aoyagi
