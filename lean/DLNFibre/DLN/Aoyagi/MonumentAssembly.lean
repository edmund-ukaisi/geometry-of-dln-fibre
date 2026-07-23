import DLNFibre.DLN.Aoyagi.LeafChartWire
import DLNFibre.DLN.Aoyagi.LeafGeometryWire
import DLNFibre.DLN.Aoyagi.Case1Wire
import DLNFibre.DLN.Aoyagi.Case2Wire
import DLNFibre.DLN.Aoyagi.CaseStepAssembly

/-!
# `DLN.Aoyagi.MonumentAssembly` — the primed composition drivers (variant B')

The primed twins of the `MonumentAtlas` composition drivers — statement-identical to their baked
counterparts, discharged via the PROVED wire leaves L6' (`leafPath_chartGeometry'`) + L8'
(`leafPath_realizesExponents'`) in place of the still-forecast `MonumentAtlas` L6/L8. The wire files
import `MonumentAtlas`, so a primed driver cannot live there (import cycle); it lives here, downstream,
retired at the summit. The drivers now consume L5' (`leaf_stepInv_of_path'`), routing the case-leaf
sources `case1/case2_preserves_stepInv` → `case1'/case2'` (onto the actively-proved boostReady +
step-form frontier). The residual `sorryAx` cone is the still-sorried L5' fold body + `MonumentAtlas`
L7/L1 — the primed footprint-sources are the baked-driver sources MINUS L6 + L8.
-/

open MeasureTheory Set Filter Topology RLCT
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi

variable {N : ℕ}

/-- Primed L5: statement-identical to `MonumentAtlas.leaf_stepInv_of_path`, with the case-leaf
cone-references swapped to `case1_preserves_stepInv'` / `case2_preserves_stepInv'` (shifts the sorryAx
source onto the actively-proved frontier — boostReady + the step-form). Fold body stays sorried. -/
@[blueprint]
theorem leaf_stepInv_of_path' (d : Fin (N + 1) → ℕ) (hN : 0 < N)
    (hpos : ∀ k, 0 < d k) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (he0 : e 0 = 0)
    (he_lin : IsLinearMap ℝ ⇑e) :
    ∃ atlas : GeoAtlasData d e, FoldProduced d e atlas ∧ FoldRealizes d e atlas ∧
      ∀ c : Fin atlas.n, ∃ q r : Fin (d (Fin.last N) * d 0) → (Fin (flatDim d) → ℝ) → ℝ,
        PrincipalInv (coreGen d e) (atlas.gmap c) (monoOf (atlas.bexp c)) q r (atlas.region c) := by
  -- map: B-L5-path-fold (primed: case leaves → case1'/case2'; fold body sorried)
  have _hc2 := case2_preserves_stepInv'' (d := d)
  have _hc1 := case1_preserves_stepInv'' (d := d)
  have _hlastclear := lastLayer_clear_preserves (d := d)
  have _hsubsume := foldStepInvAt_to_lastLayerInv (d := d)
  have _hterm_edge := terminal_edge_stepInv (d := d)
  have _hterm : TerminalBezout := terminal_bezout
  sorry

/-- Primed assembly: statement-identical to the baked `MonumentAtlas.exists_atlasRealizesExponents`,
discharged via the PROVED wire leaves L6' + L8' + the still-sorried `MonumentAtlas` L5/L7/L1; the
footprint-sources shrink by L6 + L8 vs the baked twin. -/
@[blueprint]
theorem exists_atlasRealizesExponents' (d : Fin (N + 1) → ℕ) (hN : 0 < N)
    (hpos : ∀ k, 0 < d k)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (he0 : e 0 = 0) (he_lin : IsLinearMap ℝ ⇑e) :
    ∃ res : Resolution (coreGen d e) 0, AtlasRealizesExponents d res := by
  -- L5: the geometric atlas + its FoldProduced + FoldRealizes provenance + per-chart terminal PrincipalInv.
  obtain ⟨atlas, hfold, hreal, hprin⟩ := leaf_stepInv_of_path' d hN hpos e he0 he_lin
  -- Per chart: L1 (ideal) then L6 (assemble the certified Chart), matching the atlas's data.
  have hchart : ∀ c : Fin atlas.n, ∃ chart : Chart (coreGen d e) 0,
      chart.g = atlas.gmap c ∧ chart.dom = atlas.dom c ∧ chart.nbhd = atlas.region c ∧
        chart.bexp chart.k₀ = atlas.bexp c ∧ chart.jac = atlas.jac c := by
    intro c
    obtain ⟨q, r, hpt⟩ := hprin c
    obtain ⟨hfwd, hbwd⟩ :=
      principalInv_regionRepresents (coreGen d e) (atlas.gmap c) (monoOf (atlas.bexp c)) q r
        (atlas.region c) hpt
    exact leafPath_chartGeometry' d e atlas c hfold hreal hfwd hbwd
  choose charts hg hdom _hnbhd hbexp hjac using hchart
  -- L7: the full cover of a ball by the charts' domain images (rides FoldProduced + FoldRealizes;
  --      the coordinate coverage is now bridge-free via the canonCenter pin — see the L7 banner).
  obtain ⟨ρ, hρ, hcov⟩ := leafPath_compactCover d e atlas hfold hreal
  -- L8: the exponent match (rides the FoldProduced provenance).
  obtain ⟨hspec_lb, hspec_attain⟩ :=
    leafPath_realizesExponents' d hN hpos e atlas hfold
  -- assemble the Resolution.
  haveI : Nonempty (Fin atlas.n) := ⟨⟨0, atlas.hn⟩⟩
  refine ⟨⟨atlas.n, charts, Finset.univ_nonempty, Metric.ball 0 ρ, Metric.ball_mem_nhds 0 hρ, ?_⟩,
    ?_, ?_⟩
  · -- hcover: the ball is fully covered by the charts' domain images (empty escape).
    have hsub : Metric.ball (0 : Fin (flatDim d) → ℝ) ρ ⊆ ⋃ c, (charts c).g '' (charts c).dom := by
      refine hcov.trans (Set.iUnion_mono (fun c ↦ ?_))
      rw [hg c, hdom c]
    rw [Set.diff_eq_empty.2 hsub]; exact measure_empty
  · -- AtlasRealizesExponents clause (i): transfer via the chart exponent equalities.
    intro c a ha
    rw [hjac c]
    refine hspec_lb c a ?_
    have : (charts c).bexp (charts c).k₀ = atlas.bexp c := hbexp c
    rwa [this] at ha
  · -- AtlasRealizesExponents clause (ii): transfer via the chart exponent equalities.
    intro l hl k hlk
    obtain ⟨c, a, ha, hval⟩ := hspec_attain l hl k hlk
    refine ⟨c, a, ?_, ?_⟩
    · rw [hbexp c]; exact ha
    · rw [hjac c]; exact hval

/-- Primed assembly: statement-identical to the baked
`MonumentAtlas.exists_coreResolution_via_monument`, discharged via
`exists_atlasRealizesExponents'` + the salvage adapter; footprint-sources shrink by L6 + L8. -/
@[blueprint]
theorem exists_coreResolution_via_monument' (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 0 < N)
    (hpos : ∀ k, 0 < d k) (hne : (qipFeasible d).Nonempty)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (he0 : e 0 = 0) (he_lin : IsLinearMap ℝ ⇑e) :
    ∃ res : Resolution (coreGen d e) 0,
      (∀ (c : Fin res.numCharts) (a : Fin (flatDim d)),
        a ∈ bindingAxes ((res.charts c).bexp (res.charts c).k₀) →
        qipMin d hne ≤ ((res.charts c).jac a + 1 : ℤ)) ∧
      (∃ (c : Fin res.numCharts) (a : Fin (flatDim d)),
        a ∈ bindingAxes ((res.charts c).bexp (res.charts c).k₀) ∧
        ((res.charts c).jac a + 1 : ℤ) = qipMin d hne) := by
  refine exists_hlb_hattain_of_exists_atlasRealizesExponents d hd hN hpos hne ?_
  exact exists_atlasRealizesExponents' d hN hpos e he0 he_lin

end DLNFibre.DLN.Aoyagi
