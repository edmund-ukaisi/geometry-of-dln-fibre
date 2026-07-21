import DLNFibre.Core.Analysis.RLCT.GlobalBridge
import DLNFibre.DLN.RLCT.Foundations.S1Fubini
import DLNFibre.DLN.RLCT.Validate.DeepestMinRlct

/-!
# `DLNFibre.DLN.RLCT.Foundations.GlobalHomog` — global RLCT of a homogeneous germ = local RLCT at 0

Reusable bridges connecting the **global** real-log-canonical threshold `RLCT.Global.rlctGlobal`
(Def 8.1(i), an `sSup` over globally-locally-integrable exponents, ℝ-valued) to the **local** RLCT
at the origin, for a HOMOGENEOUS continuous nonnegative germ. Two ingredients, both stated at the
weakest hypotheses that suffice and reusable outside the DLN application:

* **Homeomorphism invariance** (`globalRlctAt_comp_homeomorph`, `rlctGlobal_comp_homeomorph`): the
  polymorphic-global local RLCT and the global RLCT are unchanged by precomposition with a
  measure-preserving homeomorphism `e` (the admissible sets biject via `integrableAtFilter_map_iff`
  + `Homeomorph.map_nhds_eq` + `MeasurePreserving.map_eq`). No linearity, no homogeneity.

* **Homogeneous global = local-at-0** (`rlctGlobal_eq_rlctAt_zero_of_homogeneous`): for
  `F : (Fin n → ℝ) → ℝ` continuous, nonnegative, homogeneous of degree `D`
  (`F (c • x) = c^D * F x`), `rlctGlobal F = rlctAt F 0`. The origin is the DEEPEST point (banked
  `deepest_le_of_homogeneous_core`, ENNReal side), so every subcritical exponent that is locally
  admissible at `0` is globally admissible (`subcritical_global`, via the ENNReal↔ℝ membership
  bridges + the banked down-set `core_admissible_of_lt`); the `sSup` order argument then equates the
  two thresholds. This is the general form of the `RLCT.GlobalWitness` sum-of-squares validation,
  now for a germ whose zero-locus is a whole cone (not just `{0}`).

The ℝ-side objects live in namespace `RLCT` / `RLCT.Global` (`Core.Analysis.RLCT`); the ENNReal-side
`rlctAtOn` / deepest-point / down-set machinery lives in `DLNFibre.DLN.RLCT`. This module (in the
latter namespace) is where the two meet.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DLNFibre.DLN.RLCT

/-! ## Homeomorphism invariance of the global RLCT (no homogeneity, no linearity) -/

/-- **The polymorphic-global local admissible set transports across a measure-preserving
homeomorphism.** For `e : M ≃ₜ M'` measure-preserving (a `MeasurableEmbedding`),
`localAdmissibleExponents (F ∘ e) x = localAdmissibleExponents F (e x)`: the integrand
`(F∘e)^{-c} = F^{-c} ∘ e`, and `IntegrableAtFilter` transports via `integrableAtFilter_map_iff`
with `(𝓝 x).map e = 𝓝 (e x)` and `volume.map e = volume`. -/
theorem globalLocalAdmissible_comp_homeomorph {M M' : Type*} [MeasureSpace M] [TopologicalSpace M]
    [MeasureSpace M'] [TopologicalSpace M'] (e : M ≃ₜ M')
    (he : MeasurePreserving e volume volume) (hemb : MeasurableEmbedding e)
    (F : M' → ℝ) (x : M) :
    RLCT.Global.localAdmissibleExponents (fun w => F (e w)) x
      = RLCT.Global.localAdmissibleExponents F (e x) := by
  ext c
  simp only [RLCT.Global.mem_localAdmissibleExponents]
  have hneg : RLCT.Global.negPow (fun w => F (e w)) c = (RLCT.Global.negPow F c) ∘ e := rfl
  have hiff : IntegrableAtFilter (RLCT.Global.negPow (fun w => F (e w)) c) (𝓝 x) volume
      ↔ IntegrableAtFilter (RLCT.Global.negPow F c) (𝓝 (e x)) volume := by
    rw [hneg, ← hemb.integrableAtFilter_map_iff, e.map_nhds_eq, he.map_eq]
  rw [hiff]

/-- **The polymorphic-global local RLCT is invariant under a measure-preserving homeomorphism.**
`rlctAt (F ∘ e) x = rlctAt F (e x)` — the admissible sets coincide
(`globalLocalAdmissible_comp_homeomorph`). -/
theorem globalRlctAt_comp_homeomorph {M M' : Type*} [MeasureSpace M] [TopologicalSpace M]
    [MeasureSpace M'] [TopologicalSpace M'] (e : M ≃ₜ M')
    (he : MeasurePreserving e volume volume) (hemb : MeasurableEmbedding e)
    (F : M' → ℝ) (x : M) :
    RLCT.Global.rlctAt (fun w => F (e w)) x = RLCT.Global.rlctAt F (e x) := by
  rw [RLCT.Global.rlctAt_def, RLCT.Global.rlctAt_def,
    globalLocalAdmissible_comp_homeomorph e he hemb F x]

/-- **The global RLCT is invariant under a measure-preserving homeomorphism.**
`rlctGlobal (F ∘ e) = rlctGlobal F`: the global admissible sets coincide, `∀ x : M, P (e x) ↔ ∀ y :
M', P y` by surjectivity of `e`, and each per-point integrability transports as above. -/
theorem rlctGlobal_comp_homeomorph {M M' : Type*} [MeasureSpace M] [TopologicalSpace M]
    [MeasureSpace M'] [TopologicalSpace M'] (e : M ≃ₜ M')
    (he : MeasurePreserving e volume volume) (hemb : MeasurableEmbedding e)
    (F : M' → ℝ) :
    RLCT.Global.rlctGlobal (fun w => F (e w)) = RLCT.Global.rlctGlobal F := by
  rw [RLCT.Global.rlctGlobal_def, RLCT.Global.rlctGlobal_def]
  congr 1
  ext c
  simp only [RLCT.Global.mem_globalAdmissibleExponents]
  constructor
  · rintro ⟨hc, hall⟩
    refine ⟨hc, fun y => ?_⟩
    obtain ⟨x, rfl⟩ := e.surjective y
    have := hall x
    rwa [show RLCT.Global.negPow (fun w => F (e w)) c = (RLCT.Global.negPow F c) ∘ e from rfl,
      ← hemb.integrableAtFilter_map_iff, e.map_nhds_eq, he.map_eq] at this
  · rintro ⟨hc, hall⟩
    refine ⟨hc, fun x => ?_⟩
    have := hall (e x)
    rwa [show RLCT.Global.negPow (fun w => F (e w)) c = (RLCT.Global.negPow F c) ∘ e from rfl,
      ← hemb.integrableAtFilter_map_iff, e.map_nhds_eq, he.map_eq]

/-! ## The membership bridges (ℝ-side `localAdmissibleExponents` ↔ ENNReal-side `rlctAtOn`)

For a NONNEGATIVE germ `F` on `Fin n → ℝ`, `(F w)^{-c} = |F w|^{-c}`, so the ℝ-side admissible
predicate `IntegrableAtFilter (negPow F c) (𝓝 x)` and the ENNReal-side `weightedThreshold` integrand
`|F|^{-c}` agree. These two bridges convert between the ℝ threshold's admissible membership and the
ENNReal threshold `rlctAtOn`, so the banked deepest-point / down-set facts (ENNReal) drive the
ℝ-side reduction. -/

variable {n : ℕ}

/-- **ℝ-admissible ⟹ below the ENNReal threshold.** If `c ≥ 0` is locally admissible at `x` for a
nonnegative `F` (ℝ-side), then `(c : ℝ≥0∞) ≤ rlctAtOn F x`: the same integrable neighbourhood
witnesses membership in the `weightedThreshold` admissible set (weight `1`, `|F| = F`). -/
theorem coe_le_rlctAtOn_of_mem_localAdmissible (F : (Fin n → ℝ) → ℝ) (hnn : ∀ y, 0 ≤ F y)
    (x : Fin n → ℝ) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c ∈ RLCT.Global.localAdmissibleExponents F x) :
    ENNReal.ofReal c ≤ rlctAtOn F x := by
  obtain ⟨_, U, hU, hint⟩ := hc
  obtain ⟨Ω, hΩU, hΩopen, hxΩ⟩ := mem_nhds_iff.1 hU
  rw [rlctAtOn, weightedThreshold]
  refine le_sSup ⟨c.toNNReal, by rw [ENNReal.ofReal], Ω, hΩopen, by simpa using hxΩ, ?_⟩
  have hce : (c.toNNReal : ℝ) = c := Real.coe_toNNReal c hc0
  have : IntegrableOn (RLCT.Global.negPow F c) Ω volume := hint.mono_set hΩU
  refine this.congr_fun ?_ hΩopen.measurableSet
  intro w _
  rw [hce]
  show (F w) ^ (-c) = |F w| ^ (-c) * 1
  rw [mul_one, abs_of_nonneg (hnn w)]

/-- **Below the ENNReal threshold ⟹ ℝ-admissible.** For a measurable nonnegative `F`, if
`(c : ℝ≥0∞) < rlctAtOn F x` and `0 ≤ c`, then `c` is locally admissible at `x` (ℝ-side): the banked
`core_admissible_of_lt` produces an integrable neighbourhood of `|F|^{-c} = F^{-c}` (`F ≥ 0`). -/
theorem mem_localAdmissible_of_coe_lt_rlctAtOn (F : (Fin n → ℝ) → ℝ) (hFmeas : Measurable F)
    (hnn : ∀ y, 0 ≤ F y) (x : Fin n → ℝ) {c : ℝ} (hc0 : 0 ≤ c)
    (hlt : ENNReal.ofReal c < rlctAtOn F x) :
    c ∈ RLCT.Global.localAdmissibleExponents F x := by
  have hcoe : ((c.toNNReal : ℝ≥0∞)) < rlctAtOn F x := by rwa [ENNReal.ofReal] at hlt
  obtain ⟨Ω, hΩopen, hxΩ, hint⟩ := core_admissible_of_lt F hFmeas x c.toNNReal hcoe
  refine ⟨hc0, Ω, hΩopen.mem_nhds hxΩ, ?_⟩
  have hce : (c.toNNReal : ℝ) = c := Real.coe_toNNReal c hc0
  refine hint.congr_fun ?_ hΩopen.measurableSet
  intro w _
  rw [hce]
  show |F w| ^ (-c) = (F w) ^ (-c)
  rw [abs_of_nonneg (hnn w)]

/-! ## The subcritical bridge + the homogeneous global = local-at-0 theorem -/

/-- **Subcritical exponents are globally admissible** (homogeneous germ). For a measurable
nonnegative `F` homogeneous of degree `D`, if `c₀` is locally admissible at the origin and
`0 ≤ c < c₀`, then `c` is globally admissible: at EVERY point `x`, `(c : ℝ≥0∞) < rlctAtOn F 0 ≤
rlctAtOn F x` (deepest-point `deepest_le_of_homogeneous_core`), so `c` is locally admissible at `x`
(`mem_localAdmissible_of_coe_lt_rlctAtOn`). No paracompactness/gluing — each point gets its own
neighbourhood from the down-set. -/
theorem subcritical_global (F : (Fin n → ℝ) → ℝ) (D : ℕ) (hFmeas : Measurable F)
    (hnn : ∀ y, 0 ≤ F y) (hhom : ∀ (c : ℝ) (w : Fin n → ℝ), F (c • w) = c ^ D * F w)
    {c c₀ : ℝ} (hc0 : 0 ≤ c) (hlt : c < c₀)
    (hc₀ : c₀ ∈ RLCT.Global.localAdmissibleExponents F 0) :
    c ∈ RLCT.Global.globalAdmissibleExponents F := by
  refine ⟨hc0, fun x => ?_⟩
  -- `(c : ℝ≥0∞) < rlctAtOn F 0`, from `c < c₀` and `c₀` admissible at `0`.
  have hc₀0 : 0 ≤ c₀ := le_trans hc0 hlt.le
  have h0 : ENNReal.ofReal c₀ ≤ rlctAtOn F 0 :=
    coe_le_rlctAtOn_of_mem_localAdmissible F hnn 0 hc₀0 hc₀
  have hclt0 : ENNReal.ofReal c < rlctAtOn F 0 :=
    lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc0).mpr hlt) h0
  -- deepest point: `rlctAtOn F 0 ≤ rlctAtOn F x`.
  have hdeep : rlctAtOn F 0 ≤ rlctAtOn F x := deepest_le_of_homogeneous_core F x D hFmeas hhom
  have hcltx : ENNReal.ofReal c < rlctAtOn F x := lt_of_lt_of_le hclt0 hdeep
  have := mem_localAdmissible_of_coe_lt_rlctAtOn F hFmeas hnn x hc0 hcltx
  exact this.2

/-- **Global RLCT of a homogeneous germ equals the local RLCT at the origin.** For
`F : (Fin n → ℝ) → ℝ` continuous, nonnegative, homogeneous of degree `D`,
`rlctGlobal F = rlctAt F 0`. The `≤` is `rlctGlobal_le_rlctAt` in the pole regime; the `≥` is the
`sSup` argument driven by `subcritical_global`. In the degenerate (unbounded local admissible set)
case both sides are the documented junk `0`. -/
theorem rlctGlobal_eq_rlctAt_zero_of_homogeneous (F : (Fin n → ℝ) → ℝ) (D : ℕ)
    (hcont : Continuous F) (hnn : ∀ y, 0 ≤ F y)
    (hhom : ∀ (c : ℝ) (w : Fin n → ℝ), F (c • w) = c ^ D * F w) :
    RLCT.Global.rlctGlobal F = RLCT.Global.rlctAt F 0 := by
  have hFmeas : Measurable F := hcont.measurable
  -- `0` is globally admissible (constant germ `1` is loc-integrable everywhere on `ℝⁿ`).
  have h0glob : (0 : ℝ) ∈ RLCT.Global.globalAdmissibleExponents F := by
    refine RLCT.Global.zero_mem_globalAdmissibleExponents (fun x => ?_)
    exact ⟨Metric.ball x 1, Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos),
      integrableOn_const (hs := Metric.isBounded_ball.measure_lt_top.ne)⟩
  have h0loc : (0 : ℝ) ∈ RLCT.Global.localAdmissibleExponents F 0 :=
    RLCT.Global.globalAdmissibleExponents_subset_localAdmissibleExponents F 0 h0glob
  -- the reverse inequality `rlctAt F 0 ≤ rlctGlobal F`, via `subcritical_global` and `sSup`.
  by_cases hbdd : BddAbove (RLCT.Global.localAdmissibleExponents F 0)
  · -- pole regime: both `sSup`s are honest.
    have hle : RLCT.Global.rlctGlobal F ≤ RLCT.Global.rlctAt F 0 :=
      RLCT.Global.rlctGlobal_le_rlctAt 0 hbdd ⟨0, h0glob⟩
    have hbG : BddAbove (RLCT.Global.globalAdmissibleExponents F) :=
      hbdd.mono (RLCT.Global.globalAdmissibleExponents_subset_localAdmissibleExponents F 0)
    have hge : RLCT.Global.rlctAt F 0 ≤ RLCT.Global.rlctGlobal F := by
      rw [RLCT.Global.rlctAt_def]
      refine csSup_le ⟨0, h0loc⟩ (fun c hcA => ?_)
      refine le_of_forall_lt (fun c' hc' => ?_)
      by_cases hc'0 : c' < 0
      · exact lt_of_lt_of_le hc'0 (le_csSup hbG h0glob)
      · have hc'0' : 0 ≤ c' := le_of_not_gt hc'0
        obtain ⟨c'', hc'c'', hc''c⟩ := exists_between hc'
        have hc''0 : 0 ≤ c'' := le_trans hc'0' hc'c''.le
        have hc''G : c'' ∈ RLCT.Global.globalAdmissibleExponents F :=
          subcritical_global F D hFmeas hnn hhom hc''0 hc''c hcA
        rw [RLCT.Global.rlctGlobal_def]
        exact lt_of_lt_of_le hc'c'' (le_csSup hbG hc''G)
    exact le_antisymm hle hge
  · -- degenerate regime: local admissible unbounded ⟹ global admissible unbounded; both junk `0`.
    have hgunbdd : ¬ BddAbove (RLCT.Global.globalAdmissibleExponents F) := by
      intro hbG
      apply hbdd
      obtain ⟨B, hB⟩ := hbG
      have hB0 : (0 : ℝ) ≤ B := hB h0glob
      refine ⟨B + 1, fun c hcA => ?_⟩
      -- a subcritical exponent below any local-admissible `c` is global-admissible, hence `≤ B`.
      rcases le_or_gt c 0 with hcle | hcpos
      · linarith
      · by_contra hcB
        push_neg at hcB
        have hmid : (B + 1 + c) / 2 ∈ RLCT.Global.globalAdmissibleExponents F :=
          subcritical_global F D hFmeas hnn hhom (by linarith) (by linarith) hcA
        have := hB hmid
        linarith
    rw [RLCT.Global.rlctGlobal_def, RLCT.Global.rlctAt_def,
      Real.sSup_of_not_bddAbove hgunbdd, Real.sSup_of_not_bddAbove hbdd]

end DLNFibre.DLN.RLCT
