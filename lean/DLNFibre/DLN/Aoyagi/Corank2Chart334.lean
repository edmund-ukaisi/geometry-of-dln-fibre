import DLNFibre.DLN.Aoyagi.Corank2Realize334
import DLNFibre.DLN.Aoyagi.Corank2ChartJac
import DLNFibre.DLN.Aoyagi.LeafChartWire

/-!
# `DLN.Aoyagi.Corank2Chart334` — RUNG 5d (assembly, part 1): the concrete (3,3,4) `Chart`

Assembles the complete certified `Chart (coreGen dvec eWrap) 0` for the (3,3,4) `t=(1,0)` chart from
the banked rung-5b (`Corank2ChartJac`: Jacobian/analytic/injectivity) and part-C
(`Corank2CoreGenWrap`: the two-sided ideal identity) results. Every `Chart` field is discharged —
mirroring the general-atlas template `LeafChartWire.chart_of_collapse`, specialised to the concrete
`gWrap`/`jacWrap`/`bexpWrap`:

* geometry — `hg0` (`gWrap 0 = 0`), `hg_cont` (`continuous_gWrap`), `hg_analytic`
  (`analyticOnNhd_gWrap`), `hg_inj` (`injOn_gWrap` off `excepWrap`);
* Jacobian — `jac = jacWrap`, `unit ≡ 1`, `hjac = gWrap_hjac`;
* ideal — `hideal_fwd`/`hideal_bwd` (`hideal_coreGen_fwd`/`_bwd`, on `nbhd = univ`);
* combinatorial — `M' = 1`, `bexp = bexpWrap`, `k₀ = 0`, `hchain`/`hbind`/`hunit_mult` (`decide`).

The chart's binding data (`bindingAxes (bexpWrap 0) = {0,20}`, `jacWrap 0 = 7`, `jacWrap 20 = 8`) is
exactly what `Corank2Realize334.atlasRealizesExponents_334` consumes — so a `Resolution` built from
this chart-family realizes the (3,3,4) tree's exponents. The REMAINING rung-5d obligation is the
`Resolution` COVER (`hcover` — the coupled fan, 5c lane); see `resolution334_of_fanCover` for the
assembly reduced to that cover, and the module docstring's SPECIFY for the bridge it needs.
-/

open MeasureTheory Set Metric
open DLNFibre.Core.Aoyagi DLNFibre.Core.Aoyagi.Corank2FaithfulComposite
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap DLNFibre.DLN.Aoyagi.Corank2ChartJac

namespace DLNFibre.DLN.Aoyagi

/-- `gWrap 0 = 0` — the chart origin maps to the deepest point. `gWrap = sigmaPiv ∘ gFaithful`;
`gFaithful` is a sum of monomials with no constant term (so `gFaithful 0 = 0`) and `sigmaPiv` is a
block blow-up (`blockBlowupMap_zero`). -/
theorem gWrap_zero : gWrap (0 : Fin 21 → ℝ) = 0 := by
  have h0 : gFaithful (0 : Fin 21 → ℝ) = 0 := by
    funext k; fin_cases k <;> simp [gFaithful]
  change sigmaPiv (gFaithful 0) = 0
  rw [h0]
  exact blockBlowupMap_zero _ _

/-- **The complete concrete (3,3,4) chart** `Chart (coreGen dvec eWrap) 0`. Every field is banked;
`nbhd = univ`, `excep = excepWrap`, `unit ≡ 1`, `dom = closedBall 0 1`. -/
noncomputable def chart334 : Chart (coreGen dvec eWrap) (0 : Fin 21 → ℝ) where
  g := gWrap
  hg0 := gWrap_zero
  hg_cont := continuous_gWrap
  hg_analytic := analyticOnNhd_gWrap
  hFmeas := fun i ↦ (continuous_coreGen dvec eWrap i).measurable
  dom := closedBall 0 1
  hdom_compact := isCompact_closedBall 0 1
  hdom_zero := mem_closedBall_self zero_le_one
  nbhd := Set.univ
  hnbhd_open := isOpen_univ
  hdom_sub := subset_univ _
  excep := excepWrap
  hexcep_meas := measurableSet_excepWrap
  hexcep_null := volume_excepWrap
  hg_inj := injOn_gWrap
  M' := 1
  bexp := bexpWrap
  k₀ := 0
  hchain := fun _ _ ↦ le_refl _
  hbind := by decide
  hunit_mult := by decide
  jac := jacWrap
  unit := fun _ ↦ 1
  hunit_cont := continuousOn_const
  hunit_ne := fun _ _ ↦ one_ne_zero
  hjac := fun u _ ↦ gWrap_hjac u
  hideal_fwd := hideal_coreGen_fwd Set.univ (by simp)
  hideal_bwd := hideal_coreGen_bwd Set.univ (by simp)

@[simp] theorem chart334_g : chart334.g = gWrap := rfl
@[simp] theorem chart334_bexp_k₀ : chart334.bexp chart334.k₀ = bexpWrap 0 := rfl
@[simp] theorem chart334_jac : chart334.jac = jacWrap := rfl

/-- The chart's binding axes are `{E = 0, c11 = 20}` — the `atlasRealizesExponents_334` data. -/
theorem chart334_bindingAxes :
    bindingAxes (chart334.bexp chart334.k₀) = ({0, 20} : Finset (Fin 21)) := by
  rw [chart334_bexp_k₀]; decide

theorem chart334_jac_E : chart334.jac (0 : Fin 21) = 7 := by rw [chart334_jac]; decide
theorem chart334_jac_c11 : chart334.jac (20 : Fin 21) = 8 := by rw [chart334_jac]; decide

/-! ## The assembly, reduced to the fan cover (rung-5d seam)

The concrete `Chart` above is fully certified; the ONLY remaining `Resolution` obligation is the
coupled fan COVER. `resolution334_of_fanCover` isolates it: given a chart family (each chart with
`chart334`'s binding data — the `E`/`c11` axes with `jac = 7,8`) and its localizing cover, the full
`∃ res, AtlasRealizesExponents dvec res` (the `:311` obligation at (3,3,4)) follows, feeding
`Corank2Realize334.atlasRealizesExponents_334`.

**SPECIFY — the cover bridge the fan must supply (5c lane).** `hcover` is
`volume (U \ ⋃ c, (charts c).g '' (charts c).dom) = 0` for `U ∈ 𝓝 0`. The banked box-inflation
machinery (`LeafCoverTiling`: `FanTree.Covers f t 1 → closedBall 0 1 ⊆ t.leafImages`, and
`leafImages` = `⋃` of blow-up∘shear composites over the tree) gives a SET containment
`ball 0 ρ ⊆ leafImages`, which is STRONGER than the a.e. `hcover` (empty difference ⟹ null). So the
bridge is: (i) build the (3,3,4) `gWrap`-fan as a `FanTree 21` whose leaf path-composites are the
`K`-orbit of `gWrap` (each an isometry-conjugate, value/`jac`-preserved — heartbeat: "resolution
charts = canonical + K-symmetry orbit"); (ii) prove `Covers f gWrapFan 1` from the per-edge
box-containment (the 5c `faithfulShear_covers` shape, but at the Fin-21 (3,3,4) shears — the atom is
Fin-14 abstract, so this needs a re-instantiation or a dimension-generic `faithfulShear_covers`);
(iii) identify `⋃ c, (charts c).g '' (charts c).dom = gWrapFan.leafImages` (chart enumeration =
tree leaves, `dom` = leaf box); (iv) `covers_subset` + `U = ball 0 ρ` ⟹ `hcover`. Step (ii) is the
5c-atom connection + the genuine new work; (i),(iii),(iv) are bookkeeping over banked machinery. -/
theorem resolution334_of_fanCover (numC : ℕ) (charts : Fin numC → Chart (coreGen dvec eWrap) 0)
    (hne : (Finset.univ : Finset (Fin numC)).Nonempty) (U : Set (Fin 21 → ℝ)) (hU : U ∈ nhds 0)
    (hcover : volume (U \ ⋃ c, (charts c).g '' (charts c).dom) = 0)
    (hbind : ∀ c, bindingAxes ((charts c).bexp (charts c).k₀) = ({0, 20} : Finset (Fin 21)))
    (hjE : ∀ c, (charts c).jac (0 : Fin 21) = 7) (hjC : ∀ c, (charts c).jac (20 : Fin 21) = 8) :
    ∃ res : Resolution (coreGen dvec eWrap) 0, AtlasRealizesExponents dvec res :=
  ⟨⟨numC, charts, hne, U, hU, hcover⟩,
    atlasRealizesExponents_334 _ (0 : Fin 21) (20 : Fin 21) hbind hjE hjC⟩

/-- **The cover in SET-CONTAINMENT form** (the shape the banked `FanTree.covers_subset` produces):
if a ball around `0` is CONTAINED in the union of the fan charts' images, the full geometric
obligation follows. This discharges the measure step (`ball ⊆ ⋃ ⟹ ball \ ⋃ = ∅ ⟹ null`) so the
5c bridge only owes `ball 0 ρ ⊆ ⋃ c, (charts c).g '' (charts c).dom` — i.e. exactly
`FanTree.covers_subset gWrapFan (…)` after the chart-enumeration identification. -/
theorem resolution334_of_ballCover (numC : ℕ) (charts : Fin numC → Chart (coreGen dvec eWrap) 0)
    (hne : (Finset.univ : Finset (Fin numC)).Nonempty) (ρ : ℝ) (hρ : 0 < ρ)
    (hcov : Metric.ball (0 : Fin 21 → ℝ) ρ ⊆ ⋃ c, (charts c).g '' (charts c).dom)
    (hbind : ∀ c, bindingAxes ((charts c).bexp (charts c).k₀) = ({0, 20} : Finset (Fin 21)))
    (hjE : ∀ c, (charts c).jac (0 : Fin 21) = 7) (hjC : ∀ c, (charts c).jac (20 : Fin 21) = 8) :
    ∃ res : Resolution (coreGen dvec eWrap) 0, AtlasRealizesExponents dvec res := by
  refine resolution334_of_fanCover numC charts hne (Metric.ball 0 ρ)
    (Metric.ball_mem_nhds 0 hρ) ?_ hbind hjE hjC
  rw [Set.diff_eq_empty.mpr hcov]; exact measure_empty

/-- **The PER-CHART fan seam** (gate2's 5d flag). For a coord-permuted FAN presented as multiple
`Resolution.charts` (each chart binding on its OWN axes), the uniform `bindingAxes = {0,20}` is
FALSE; this form demands only the fan-invariant VALUE content — each chart's binding-axis value is
`8` or `9`, and some chart attains `8 = minAdm`. Feeds `atlasRealizesExponents_334_ofValues`. -/
theorem resolution334_of_fanCover_ofValues (numC : ℕ)
    (charts : Fin numC → Chart (coreGen dvec eWrap) 0)
    (hne : (Finset.univ : Finset (Fin numC)).Nonempty) (U : Set (Fin 21 → ℝ)) (hU : U ∈ nhds 0)
    (hcover : volume (U \ ⋃ c, (charts c).g '' (charts c).dom) = 0)
    (hval : ∀ (c : Fin numC) (a : Fin 21),
        a ∈ bindingAxes ((charts c).bexp (charts c).k₀) →
        (charts c).jac a + 1 = 8 ∨ (charts c).jac a + 1 = 9)
    (hmin : ∃ (c : Fin numC) (a : Fin 21),
        a ∈ bindingAxes ((charts c).bexp (charts c).k₀) ∧ (charts c).jac a + 1 = 8) :
    ∃ res : Resolution (coreGen dvec eWrap) 0, AtlasRealizesExponents dvec res :=
  ⟨⟨numC, charts, hne, U, hU, hcover⟩, atlasRealizesExponents_334_ofValues _ hval hmin⟩

/-- The per-chart seam in SET-CONTAINMENT (`ball ⊆ ⋃ images`) form — the recommended fan cover seam:
the 5c bridge owes `ball 0 ρ ⊆ ⋃ c, (charts c).g '' (charts c).dom` plus, per chart, its binding
values (`{8,9}`, fan-invariant under the coord-perm `jac`). Delegates to `..._fanCover_ofValues`. -/
theorem resolution334_of_ballCover_ofValues (numC : ℕ)
    (charts : Fin numC → Chart (coreGen dvec eWrap) 0)
    (hne : (Finset.univ : Finset (Fin numC)).Nonempty) (ρ : ℝ) (hρ : 0 < ρ)
    (hcov : Metric.ball (0 : Fin 21 → ℝ) ρ ⊆ ⋃ c, (charts c).g '' (charts c).dom)
    (hval : ∀ (c : Fin numC) (a : Fin 21),
        a ∈ bindingAxes ((charts c).bexp (charts c).k₀) →
        (charts c).jac a + 1 = 8 ∨ (charts c).jac a + 1 = 9)
    (hmin : ∃ (c : Fin numC) (a : Fin 21),
        a ∈ bindingAxes ((charts c).bexp (charts c).k₀) ∧ (charts c).jac a + 1 = 8) :
    ∃ res : Resolution (coreGen dvec eWrap) 0, AtlasRealizesExponents dvec res := by
  refine resolution334_of_fanCover_ofValues numC charts hne (Metric.ball 0 ρ)
    (Metric.ball_mem_nhds 0 hρ) ?_ hval hmin
  rw [Set.diff_eq_empty.mpr hcov]; exact measure_empty

end DLNFibre.DLN.Aoyagi
