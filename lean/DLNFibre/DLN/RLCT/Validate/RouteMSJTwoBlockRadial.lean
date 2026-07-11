import DLNFibre.DLN.RLCT.Validate.RouteMSJRadialInt
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJTwoBlockRadial` — the coupled two-block radial estimate

**Thread `genm-vsa` (aoyagi-full), step (a) — the genuinely-new custom piece of the front-first
coupled majorant.** After diagonalising the tail Gram `PPᵀ` and enclosing the front box in a ball,
the coupled front integrand is a two-weighted-block radial power. On the dominance sector
`{σ_{r−1} ≥ κ}` the collapsing block carries the small singular value `σ = σ_r`; the stable blocks
carry the `O(1)` weight `κ`. This module proves the coupled bound

    ∫_{ball_u R × ball_v R} (κ²‖u‖² + σ²‖v‖²)^{−c'}  ≤  C · σ^{−α}

with `u ∈ ℝ^{d_u}` (the `d_u = m₀(r−1)` stable directions) and `v ∈ ℝ^{d_v}` (the `d_v = m₀`
collapsing directions). The Frobenius–Gram diagonalisation `‖A₀P‖_F² = ∑_j s_j² ‖(A₀Q)_{·j}‖²`
makes `d_u = m₀(r−1)`, `d_v = m₀` EXACT (for `(3,3,3,4)`: `d_u = 6`, `d_v = 3`).

**The ε-form** (operator-approved, `genm-vsa` scope): `twoBlock_radial_le` delivers
`≤ C · σ^{−α'}` with `C < ⊤` **σ-independent**, for every `α'` with `max(0, 2c'−d_u) < α' < d_v` and on
the bounded sector `0 < σ ≤ B`. This is the honest majorant family: at the borderline `2c' = d_u` (for
`(3,3,3,4)`, `c' = 3`) the *exact* `≤ C·σ⁰` is FALSE (a log divergence), but the ε-form is TRUE for any
`α' > 0` there and composes with LAYER 2 (which needs `α' < 1`). The `σ ≤ B` bound is load-bearing for the
σ-independent `C`: for `α' > 2c'` (a genuine sub-regime) the exact `∫·σ^{α'}` diverges as `σ → ∞`, so no
`C` uniform over all `σ > 0` exists there; the wire-in supplies `B` (the tail box bounds `σ_r`). The
single-exponent sharp form `twoBlock_radial_scale_le` is σ-independent for all `σ > 0` with no bound.

**Route (coupled-front-first, no `σ^{−m₀}` whole-line artifact).** For the sharp scale form
(`d_u < 2c'`): enlarge the `u`-ball to `ℝ^{d_u}` (integrand `≥ 0`), Tonelli-split over `v`, then the
per-`v` inner `u`-integral scales out (`map_addHaar_smul`, one Haar dilation `u = (σ‖v‖/κ)•ŵ`) to
`κ^{−d_u} · K · (σ‖v‖)^{−(2c'−d_u)}`, where `K = ∫_{ℝ^{d_u}} (1+‖z‖²)^{−c'}` is finite by the
Japanese bracket (`integrable_rpow_neg_one_add_norm_sq`, needs `d_u < 2c'`). The remaining
`∫_{ball_v} ‖v‖^{−(2c'−d_u)}` is finite by the banked radial leaf
(`lintegral_norm_rpow_neg_ball_lt_top`, needs `2c'−d_u < d_v`). The ε-form then dominates a general
`c'` by the sharp form at `c'' = (d_u+α')/2` via `X^{−c'} ≤ M^{c''−c'} X^{−c''}` on the bounded box.

Network-free (pure Euclidean measure theory over Mathlib + the banked radial leaf). Intended axiom
footprint `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Metric
open scoped ENNReal

/-- **Haar dilation of a lower integral** on Euclidean space: `∫ F(r • x) = r^{−n} · ∫ F` for
`r > 0`. The `n`-fold Jacobian of `x ↦ r • x` on `ℝⁿ`. -/
private theorem lintegral_comp_smul_euclidean {n : ℕ} {r : ℝ} (hr : 0 < r)
    {F : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ x, F (r • x)) = ENNReal.ofReal ((r ^ n)⁻¹) * ∫⁻ x, F x := by
  have hmap : Measure.map (r • ·) (volume : Measure (EuclideanSpace ℝ (Fin n)))
      = ENNReal.ofReal ((r ^ n)⁻¹) • volume := by
    have h := Measure.map_addHaar_smul (volume : Measure (EuclideanSpace ℝ (Fin n))) (ne_of_gt hr)
    rw [finrank_euclideanSpace_fin] at h
    rw [h, abs_of_nonneg (by positivity)]
  calc (∫⁻ x, F (r • x))
      = ∫⁻ y, F y ∂(Measure.map (r • ·) (volume : Measure (EuclideanSpace ℝ (Fin n)))) :=
        (lintegral_map hF (measurable_const_smul r)).symm
    _ = ∫⁻ y, F y ∂(ENNReal.ofReal ((r ^ n)⁻¹) • volume) := by rw [hmap]
    _ = ENNReal.ofReal ((r ^ n)⁻¹) * ∫⁻ y, F y := lintegral_smul_measure _ _

/-- **The Japanese-bracket constant** `K = ∫_{ℝ^{d_u}} (1+‖z‖²)^{−c}`, finite when `d_u < 2c`. -/
private noncomputable def Kbracket (du : ℕ) (c : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : EuclideanSpace ℝ (Fin du), ENNReal.ofReal ((1 + ‖z‖ ^ 2) ^ (-c))

private theorem Kbracket_lt_top {du : ℕ} {c : ℝ} (hdu : (du : ℝ) < 2 * c) :
    Kbracket du c < ⊤ := by
  have hInt : Integrable (fun z : EuclideanSpace ℝ (Fin du) ↦ (1 + ‖z‖ ^ 2) ^ (-(2 * c) / 2)) := by
    apply integrable_rpow_neg_one_add_norm_sq
    rwa [finrank_euclideanSpace_fin]
  have hexp : (fun z : EuclideanSpace ℝ (Fin du) ↦ (1 + ‖z‖ ^ 2) ^ (-(2 * c) / 2))
      = fun z : EuclideanSpace ℝ (Fin du) ↦ (1 + ‖z‖ ^ 2) ^ (-c) := by
    funext z; congr 1; ring
  rw [hexp] at hInt
  have hnn : ∀ z : EuclideanSpace ℝ (Fin du), (0:ℝ) ≤ (1 + ‖z‖ ^ 2) ^ (-c) :=
    fun z => Real.rpow_nonneg (by positivity) _
  have heq : (∫⁻ z : EuclideanSpace ℝ (Fin du), ENNReal.ofReal ((1 + ‖z‖ ^ 2) ^ (-c)))
      = ∫⁻ z : EuclideanSpace ℝ (Fin du), ‖(1 + ‖z‖ ^ 2) ^ (-c)‖ₑ :=
    lintegral_congr (fun z => (Real.enorm_eq_ofReal (hnn z)).symm)
  rw [Kbracket, heq]
  exact hInt.hasFiniteIntegral

/-- **The per-`v` inner-`u` scale-out (separated form).** For `v ≠ 0`, the full-space `u`-integral
of the coupled weight is `ofReal(σ^{−α}) · ofReal(κ^{−d_u}) · ofReal(‖v‖^{−α}) · K` with
`α = 2c − d_u` (one Haar dilation `u = (σ‖v‖/κ)•ŵ`). -/
private theorem inner_u_scaleout {du dv : ℕ} {κ σ c : ℝ} (hκ : 0 < κ) (hσ : 0 < σ)
    (v : EuclideanSpace ℝ (Fin dv)) (hv : v ≠ 0) :
    (∫⁻ u : EuclideanSpace ℝ (Fin du),
        ENNReal.ofReal ((κ ^ 2 * ‖u‖ ^ 2 + σ ^ 2 * ‖v‖ ^ 2) ^ (-c)))
      = ENNReal.ofReal (σ ^ (-(2 * c - (du : ℝ)))) * ENNReal.ofReal (κ ^ (-(du : ℝ)))
          * ENNReal.ofReal (‖v‖ ^ (-(2 * c - (du : ℝ)))) * Kbracket du c := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set b : ℝ := σ * ‖v‖ with hb
  have hbpos : 0 < b := mul_pos hσ hvpos
  have hb2 : σ ^ 2 * ‖v‖ ^ 2 = b ^ 2 := by rw [hb]; ring
  set r : ℝ := b / κ with hr
  have hrpos : 0 < r := div_pos hbpos hκ
  set F : EuclideanSpace ℝ (Fin du) → ℝ≥0∞ :=
    fun u => ENNReal.ofReal ((κ ^ 2 * ‖u‖ ^ 2 + σ ^ 2 * ‖v‖ ^ 2) ^ (-c)) with hFdef
  have hFmeas : Measurable F := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c)) (by fun_prop)
    exact ((measurable_norm.pow_const 2).const_mul (κ ^ 2)).add_const (σ ^ 2 * ‖v‖ ^ 2)
  have hpt : ∀ u : EuclideanSpace ℝ (Fin du),
      F (r • u) = ENNReal.ofReal (b ^ (-(2 * c))) * ENNReal.ofReal ((1 + ‖u‖ ^ 2) ^ (-c)) := by
    intro u
    simp only [hFdef]
    have hnorm : ‖r • u‖ ^ 2 = r ^ 2 * ‖u‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, mul_pow]
    have hbase : κ ^ 2 * ‖r • u‖ ^ 2 + σ ^ 2 * ‖v‖ ^ 2 = b ^ 2 * (1 + ‖u‖ ^ 2) := by
      rw [hnorm, hb2, hr]; field_simp; ring
    rw [hbase, Real.mul_rpow (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
    congr 1
    rw [← Real.rpow_natCast b 2, ← Real.rpow_mul (le_of_lt hbpos)]
    norm_num
  have hscale := lintegral_comp_smul_euclidean (n := du) hrpos hFmeas
  rw [funext hpt, lintegral_const_mul _ (by fun_prop)] at hscale
  have hK : (∫⁻ u : EuclideanSpace ℝ (Fin du), ENNReal.ofReal ((1 + ‖u‖ ^ 2) ^ (-c)))
      = Kbracket du c := rfl
  rw [hK] at hscale
  -- hscale : ofReal(b^{-2c}) * K = ofReal((r^du)⁻¹) * ∫ F
  have hrdu_pos : (0 : ℝ) < r ^ du := by positivity
  have hcancel : ENNReal.ofReal (r ^ du) * ENNReal.ofReal ((r ^ du)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (le_of_lt hrdu_pos), mul_inv_cancel₀ (ne_of_gt hrdu_pos),
      ENNReal.ofReal_one]
  -- the real coefficient identity
  have hcoef : r ^ du * b ^ (-(2 * c))
      = σ ^ (-(2 * c - (du : ℝ))) * κ ^ (-(du : ℝ)) * ‖v‖ ^ (-(2 * c - (du : ℝ))) := by
    have hrdu : r ^ du = b ^ (du : ℝ) * κ ^ (-(du : ℝ)) := by
      rw [hr, div_pow, ← Real.rpow_natCast b du, ← Real.rpow_natCast κ du,
        Real.rpow_neg (le_of_lt hκ), div_eq_mul_inv]
    rw [hrdu, mul_assoc, mul_comm (κ ^ (-(du : ℝ))) (b ^ (-(2 * c))), ← mul_assoc,
      ← Real.rpow_add hbpos]
    rw [show (du : ℝ) + -(2 * c) = -(2 * c - (du : ℝ)) from by ring, hb,
      Real.mul_rpow (le_of_lt hσ) (le_of_lt hvpos)]
    ring
  calc (∫⁻ u, F u)
      = ENNReal.ofReal (r ^ du) * (ENNReal.ofReal ((r ^ du)⁻¹) * (∫⁻ u, F u)) := by
        rw [← mul_assoc, hcancel, one_mul]
    _ = ENNReal.ofReal (r ^ du) * (ENNReal.ofReal (b ^ (-(2 * c))) * Kbracket du c) := by
        rw [← hscale]
    _ = ENNReal.ofReal (r ^ du * b ^ (-(2 * c))) * Kbracket du c := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt hrdu_pos)]
    _ = ENNReal.ofReal (σ ^ (-(2 * c - (du : ℝ)))) * ENNReal.ofReal (κ ^ (-(du : ℝ)))
          * ENNReal.ofReal (‖v‖ ^ (-(2 * c - (du : ℝ)))) * Kbracket du c := by
        rw [hcoef, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]

/-- **The σ-independent constant** of the sharp scale bound. -/
private noncomputable def twoBlockConst (du dv : ℕ) (c κ R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (κ ^ (-(du : ℝ))) * Kbracket du c
    * ∫⁻ v in Metric.ball (0 : EuclideanSpace ℝ (Fin dv)) R,
        ENNReal.ofReal (‖v‖ ^ (-(2 * c - (du : ℝ))))

private theorem twoBlockConst_lt_top {du dv : ℕ} (hdv : 1 ≤ dv) {c κ R : ℝ}
    (hlo : (du : ℝ) < 2 * c) (hhi : 2 * c < (du : ℝ) + dv) : twoBlockConst du dv c κ R < ⊤ := by
  have hα : 2 * c - (du : ℝ) < dv := by linarith
  refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Kbracket_lt_top hlo)) ?_
  exact lintegral_norm_rpow_neg_ball_lt_top hdv hα R

/-- **Sharp single-exponent two-block radial bound.** For `κ, σ > 0` (any `R`),
`∫_{ball_u R × ball_v R} (κ²‖u‖² + σ²‖v‖²)^{−c} ≤ ofReal(σ^{−(2c−d_u)}) · C`, with `C` the
σ-independent `twoBlockConst`. The exact scale-out holds unconditionally; `C < ⊤` precisely on the
regime `d_u < 2c < d_u + d_v` (`twoBlockConst_lt_top`). -/
theorem twoBlock_radial_scale_le {du dv : ℕ} (hdv : 1 ≤ dv) {c κ σ R : ℝ}
    (hκ : 0 < κ) (hσ : 0 < σ) :
    (∫⁻ p in (Metric.ball (0 : EuclideanSpace ℝ (Fin du)) R
                ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin dv)) R),
        ENNReal.ofReal ((κ ^ 2 * ‖p.1‖ ^ 2 + σ ^ 2 * ‖p.2‖ ^ 2) ^ (-c)))
      ≤ ENNReal.ofReal (σ ^ (-(2 * c - (du : ℝ)))) * twoBlockConst du dv c κ R := by
  set E_u := EuclideanSpace ℝ (Fin du)
  set E_v := EuclideanSpace ℝ (Fin dv)
  set F : E_u × E_v → ℝ≥0∞ :=
    fun p => ENNReal.ofReal ((κ ^ 2 * ‖p.1‖ ^ 2 + σ ^ 2 * ‖p.2‖ ^ 2) ^ (-c)) with hFdef
  have hFmeas : Measurable F := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c)) (by fun_prop)
    exact (((measurable_norm.comp measurable_fst).pow_const 2).const_mul (κ ^ 2)).add
      (((measurable_norm.comp measurable_snd).pow_const 2).const_mul (σ ^ 2))
  -- 1. enlarge the u-ball to the full space
  have hsub : (Metric.ball (0 : E_u) R ×ˢ Metric.ball (0 : E_v) R)
      ⊆ (Set.univ ×ˢ Metric.ball (0 : E_v) R) :=
    Set.prod_mono (Set.subset_univ _) (le_refl _)
  have hstep1 : (∫⁻ p in (Metric.ball (0 : E_u) R ×ˢ Metric.ball (0 : E_v) R), F p)
      ≤ ∫⁻ p in (Set.univ ×ˢ Metric.ball (0 : E_v) R), F p := lintegral_mono_set hsub
  -- 2. Tonelli, outer v
  have hTon : (∫⁻ p in (Set.univ ×ˢ Metric.ball (0 : E_v) R), F p)
      = ∫⁻ v in Metric.ball (0 : E_v) R, ∫⁻ u, F (u, v) := by
    rw [Measure.volume_eq_prod E_u E_v, ← Measure.prod_restrict, Measure.restrict_univ,
      lintegral_prod_symm _ hFmeas.aemeasurable]
  -- 3. per-v scale-out (a.e. in v, off the null point v = 0)
  set RHS : E_v → ℝ≥0∞ := fun v => ENNReal.ofReal (σ ^ (-(2 * c - (du : ℝ))))
      * ENNReal.ofReal (κ ^ (-(du : ℝ))) * ENNReal.ofReal (‖v‖ ^ (-(2 * c - (du : ℝ))))
      * Kbracket du c with hRHSdef
  have hae : (fun v => ∫⁻ u, F (u, v)) =ᵐ[volume.restrict (Metric.ball (0 : E_v) R)] RHS := by
    haveI : Nontrivial E_v := by
      apply Module.nontrivial_of_finrank_pos (R := ℝ)
      rw [finrank_euclideanSpace_fin]; omega
    have hane : ∀ᵐ v ∂(volume : Measure E_v), v ≠ 0 := by
      rw [ae_iff]
      simp only [not_ne_iff, Set.setOf_eq_eq_singleton]
      exact measure_singleton 0
    refine (ae_restrict_iff' measurableSet_ball).mpr ?_
    filter_upwards [hane] with v hv _
    simp only [hFdef, hRHSdef]
    exact inner_u_scaleout hκ hσ v hv
  refine hstep1.trans ?_
  rw [hTon, lintegral_congr_ae hae, hRHSdef]
  -- 4. pull constants out of the ball_v integral
  refine le_of_eq ?_
  rw [show (fun v : E_v => ENNReal.ofReal (σ ^ (-(2 * c - (du : ℝ))))
        * ENNReal.ofReal (κ ^ (-(du : ℝ))) * ENNReal.ofReal (‖v‖ ^ (-(2 * c - (du : ℝ))))
        * Kbracket du c)
      = fun v : E_v => (ENNReal.ofReal (σ ^ (-(2 * c - (du : ℝ)))))
        * (ENNReal.ofReal (κ ^ (-(du : ℝ))) * Kbracket du c
            * ENNReal.ofReal (‖v‖ ^ (-(2 * c - (du : ℝ))))) from by
      funext v; ring]
  rw [lintegral_const_mul _ (by fun_prop), twoBlockConst]
  rw [lintegral_const_mul _ (by fun_prop)]

/-- **The coupled two-block radial estimate — ε-form** (`genm-vsa` step (a) crux). For every `α'`
with `max(0, 2c'−d_u) < α'` and `α' < d_v`, `0 < c'`, `κ, R > 0`, and an upper bound `0 < σ ≤ B` on the
small singular value: `∫_{ball_u R × ball_v R} (κ²‖u‖² + σ²‖v‖²)^{−c'} ≤ ofReal(σ^{−α'}) · C` with
`C < ⊤` a **σ-independent** constant (it depends on `B, κ, R, c', α', d_u, d_v`, not on `σ`). Covers the
borderline `2c' = d_u` (log point) with any `α' > 0`. The `σ ≤ B` bound is load-bearing for the
σ-uniform `C`: without it the exact `∫·σ^{α'}` grows unboundedly as `σ → ∞` in the sub-regime `α' > 2c'`,
so a `C` valid for all `σ > 0` does not exist there; the σ-independent `C` the wire-in pulls out of the
tail integral holds on the bounded sector `σ ≤ B`. (The sharp single-exponent `twoBlock_radial_scale_le`
is σ-independent for all `σ > 0` without a bound.) -/
theorem twoBlock_radial_le {du dv : ℕ} (hdv : 1 ≤ dv) {c' α' κ σ B R : ℝ}
    (hc' : 0 < c') (hκ : 0 < κ) (hσ0 : 0 < σ) (hσB : σ ≤ B) (hR : 0 < R)
    (hα0 : 0 < α') (hαlo : 2 * c' - (du : ℝ) < α') (hαhi : α' < dv) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      (∫⁻ p in (Metric.ball (0 : EuclideanSpace ℝ (Fin du)) R
                  ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin dv)) R),
          ENNReal.ofReal ((κ ^ 2 * ‖p.1‖ ^ 2 + σ ^ 2 * ‖p.2‖ ^ 2) ^ (-c')))
        ≤ ENNReal.ofReal (σ ^ (-α')) * C := by
  -- choose c'' = (d_u + α')/2 : sharp exponent whose α is exactly α'
  set c'' : ℝ := ((du : ℝ) + α') / 2 with hc''
  have hlo : (du : ℝ) < 2 * c'' := by rw [hc'']; linarith
  have hhi : 2 * c'' < (du : ℝ) + dv := by rw [hc'']; linarith
  have hα_eq : 2 * c'' - (du : ℝ) = α' := by rw [hc'']; ring
  have hc'c'' : c' < c'' := by rw [hc'']; linarith
  -- σ-FREE box constant M = R²(κ² + B²) bounding the base on the box (uses σ ≤ B) — this is what
  -- makes the constant C σ-independent.
  set M : ℝ := R ^ 2 * (κ ^ 2 + B ^ 2) with hM
  have hMpos : 0 < M := by rw [hM]; positivity
  have hσ2 : σ ^ 2 ≤ B ^ 2 := by nlinarith [hσ0, hσB]
  -- pointwise domination on the box
  have hdom : ∀ p ∈ (Metric.ball (0 : EuclideanSpace ℝ (Fin du)) R
        ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin dv)) R),
      ENNReal.ofReal ((κ ^ 2 * ‖p.1‖ ^ 2 + σ ^ 2 * ‖p.2‖ ^ 2) ^ (-c'))
        ≤ ENNReal.ofReal (M ^ (c'' - c'))
            * ENNReal.ofReal ((κ ^ 2 * ‖p.1‖ ^ 2 + σ ^ 2 * ‖p.2‖ ^ 2) ^ (-c'')) := by
    rintro ⟨u, v⟩ hp
    simp only [Set.mem_prod, mem_ball_zero_iff] at hp
    obtain ⟨hu, hv⟩ := hp
    set X : ℝ := κ ^ 2 * ‖u‖ ^ 2 + σ ^ 2 * ‖v‖ ^ 2 with hX
    have hXnn : 0 ≤ X := by rw [hX]; positivity
    have hXM : X ≤ M := by
      rw [hX, hM]
      have h1 : ‖u‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg u, le_of_lt hu]
      have h2 : ‖v‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg v, le_of_lt hv]
      nlinarith [sq_nonneg κ, sq_nonneg σ, h1, h2, hσ2, norm_nonneg u, norm_nonneg v, sq_nonneg R]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hMpos) _)]
    apply ENNReal.ofReal_le_ofReal
    rcases eq_or_lt_of_le hXnn with hX0 | hXpos
    · rw [← hX0, Real.zero_rpow (by linarith : -c' ≠ 0),
        Real.zero_rpow (by linarith : -c'' ≠ 0), mul_zero]
    · have hsplit : X ^ (-c') = X ^ (-c'') * X ^ (c'' - c') := by
        rw [← Real.rpow_add hXpos]; congr 1; ring
      rw [hsplit, mul_comm]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (le_of_lt hXpos) _)
      exact Real.rpow_le_rpow (le_of_lt hXpos) hXM (by linarith)
  -- assemble via the sharp scale bound at c''
  refine ⟨ENNReal.ofReal (M ^ (c'' - c')) * twoBlockConst du dv c'' κ R, ?_, ?_⟩
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (twoBlockConst_lt_top hdv hlo hhi)
  · calc (∫⁻ p in (Metric.ball (0 : EuclideanSpace ℝ (Fin du)) R
                    ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin dv)) R),
            ENNReal.ofReal ((κ ^ 2 * ‖p.1‖ ^ 2 + σ ^ 2 * ‖p.2‖ ^ 2) ^ (-c')))
        ≤ ∫⁻ p in (Metric.ball (0 : EuclideanSpace ℝ (Fin du)) R
                    ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin dv)) R),
            ENNReal.ofReal (M ^ (c'' - c'))
              * ENNReal.ofReal ((κ ^ 2 * ‖p.1‖ ^ 2 + σ ^ 2 * ‖p.2‖ ^ 2) ^ (-c'')) :=
          lintegral_mono_ae (ae_restrict_of_forall_mem
            (measurableSet_ball.prod measurableSet_ball) hdom)
      _ = ENNReal.ofReal (M ^ (c'' - c'))
            * ∫⁻ p in (Metric.ball (0 : EuclideanSpace ℝ (Fin du)) R
                    ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin dv)) R),
              ENNReal.ofReal ((κ ^ 2 * ‖p.1‖ ^ 2 + σ ^ 2 * ‖p.2‖ ^ 2) ^ (-c'')) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (M ^ (c'' - c'))
            * (ENNReal.ofReal (σ ^ (-(2 * c'' - (du : ℝ)))) * twoBlockConst du dv c'' κ R) := by
          gcongr
          exact twoBlock_radial_scale_le hdv hκ hσ0
      _ = ENNReal.ofReal (σ ^ (-α'))
            * (ENNReal.ofReal (M ^ (c'' - c')) * twoBlockConst du dv c'' κ R) := by
          rw [hα_eq]; ring

end DLNFibre.DLN.RLCT
