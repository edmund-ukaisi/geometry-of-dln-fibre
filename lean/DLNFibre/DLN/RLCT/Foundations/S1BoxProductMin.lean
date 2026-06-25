import DLNFibre.DLN.RLCT.Foundations.S1WeightedProductMin

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1BoxProductMin` — the BOX-form weighted product-min (R1, item 1)

The corrected per-chart object for the per-node blow-up cover (cert-104b §4, R1 transport-producer
lane; the gate-found correction to the point-lemma `weightedProductMin_mono1D_of_ne`).

## Why a box, not a point (the gate finding, 2026-06-23)
The per-node blow-up cover sums (via `g5_flat_cover`) per-chart integrals over a **chart-domain box**
`V_i \ Z_i` whose fibre `φ_i⁻¹{0}` is the **exceptional divisor** `{y₀ = 0}` (a hyperplane), NOT the
point `(0,0)`. The point-threshold lemma `weightedProductMin_mono1D_of_ne` computes the threshold AT
the point and does NOT control the per-chart box integral. The honest per-chart object is the
**box-integrability** of the pulled-back integrand

  `g(y₀, z) = |y₀²·K(z)|^{−c'} · |y₀|^e`   (`e = mk − 1`, `K = core`, the Jacobian `|y₀|^e` weight)

over a rectangle `Iy ×ˢ Vz`. By the rectangle Fubini split (`wpm_rect_split`-style, re-derived here)
this factorises into

  `(∫ over Iy of |y₀²|^{−c'}·|y₀|^e)  ·  (∫ over Vz of |K|^{−c'})`,

so the box-integrand is integrable on the rectangle **iff** both factor-integrals are finite — i.e.
`c' < (e+1)/2` (the `y₀`-side, `weightedMono1D_admissible_iff`) AND `|K|^{−c'}` integrable on `Vz`
(the core box-integrability). This file delivers exactly that rectangle-integrability characterisation,
the direction the cover's `≥`/`≤` legs consume: it feeds the finite-summand cover assembly (the GE leg)
and, in reverse, the per-chart below-threshold extraction (the LE leg).

The threshold VALUE `min{(e+1)/2, rlctAtOn K 0}` is already proved at the point
(`weightedProductMin_mono1D_of_ne`); here we expose the integrability over a fixed rectangle, which is
what the cover machinery (`g5_flat_cover`, fixed `V_i \ Z_i` domains) needs.

Axiom-free target (only `propext`/`Classical.choice`/`Quot.sound`).
-/

open MeasureTheory Set Real
open scoped ENNReal Topology BigOperators
namespace DLNFibre.DLN.RLCT

variable {Z : Type*} [MeasureSpace Z] [TopologicalSpace Z] [Zero Z]
    [SFinite (volume : Measure Z)] [BorelSpace Z] [SecondCountableTopology Z]

/-! ## 1. The rectangle Fubini split for the blow-up pullback integrand -/

/-- **The blow-up pullback rectangle split.** The per-chart pullback integrand
`|y₀²·K(z)|^{−c'}·|y₀|^e` factorises over a rectangle `Iy ×ˢ Vz` into the `y₀`-side weighted integral
`∫_{Iy} |y₀²|^{−c'}·|y₀|^e` and the core box-integral `∫_{Vz} |K|^{−c'}`. (The box analog of
`wpm_rect_split` with `G = (·)²`, `ρ = |·|^e`, `H = K`.) -/
theorem boxpm_rect_split (K : Z → ℝ) (hKm : Measurable K) (e : ℕ) (c' : ℝ)
    (Iy : Set ℝ) (Vz : Set Z) :
    ∫⁻ p in Iy ×ˢ Vz, ENNReal.ofReal (|p.1 ^ 2 * K p.2| ^ (-c') * |p.1| ^ e)
      = (∫⁻ y in Iy, ENNReal.ofReal (|y ^ 2| ^ (-c') * |y| ^ e))
        * (∫⁻ z in Vz, ENNReal.ofReal (|K z| ^ (-c'))) := by
  have hsplit : (fun p : ℝ × Z => ENNReal.ofReal (|p.1 ^ 2 * K p.2| ^ (-c') * |p.1| ^ e))
      = (fun p => ENNReal.ofReal (|p.1 ^ 2| ^ (-c') * |p.1| ^ e)
          * ENNReal.ofReal (|K p.2| ^ (-c'))) := by
    funext p
    rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (by positivity))]
    congr 1
    rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    ring
  rw [hsplit, Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact lintegral_prod_mul
    ((by fun_prop : Measurable (fun y : ℝ => ENNReal.ofReal (|y ^ 2| ^ (-c') * |y| ^ e))).aemeasurable)
    ((by fun_prop : Measurable (fun z : Z => ENNReal.ofReal (|K z| ^ (-c')))).aemeasurable)

/-! ## 1b. The `y₀`-side box integrability (the divisor factor on a bounded interval) -/

/-- The `y₀`-side integrand `|y²|^{−c'}·|y|^e` agrees with `|y|^{e − 2c'}` off the origin. -/
private theorem boxpm_y_integrand_eq (e : ℕ) (c' : ℝ) {y : ℝ} (hy : y ≠ 0) :
    |y ^ 2| ^ (-c') * |y| ^ e = |y| ^ ((e : ℝ) - 2 * c') := by
  have hyabs : 0 < |y| := abs_pos.2 hy
  have h2 : |y ^ 2| = |y| ^ 2 := by rw [abs_pow]
  rw [h2, ← Real.rpow_natCast |y| 2, ← Real.rpow_natCast |y| e,
    ← Real.rpow_mul hyabs.le, ← Real.rpow_add hyabs]
  ring_nf

/-- **The `y₀`-side box integrability.** For `c' < (e+1)/2` and any bounded measurable `Iy ⊆ ℝ`, the
divisor integrand `|y²|^{−c'}·|y|^e` is integrable on `Iy`. Encloses `Iy` in a symmetric interval
`Icc (−R) R` and reduces to `|y|^{e−2c'}` integrability (`abs_rpow_integrableOn_Icc_symm`, the iff at
`e − 2c' > −1 ⟺ c' < (e+1)/2`), off the null origin. -/
theorem boxpm_y_integrableOn (e : ℕ) (c' : ℝ) (hc'lt : c' < ((e : ℝ) + 1) / 2)
    (Iy : Set ℝ) (hIy : MeasurableSet Iy) (hIybdd : Bornology.IsBounded Iy) :
    IntegrableOn (fun y : ℝ => |y ^ 2| ^ (-c') * |y| ^ e) Iy volume := by
  -- enclose `Iy ⊆ Icc (−R') R'` with `R' = |R| + 1 > 0`.
  obtain ⟨R, hR⟩ := hIybdd.subset_closedBall 0
  set R' : ℝ := |R| + 1 with hR'def
  have hRpos : 0 < R' := by rw [hR'def]; positivity
  have hsub : Iy ⊆ Icc (-R') R' := by
    intro x hx
    have hxR := hR hx
    rw [Real.closedBall_eq_Icc] at hxR
    simp only [zero_sub, zero_add, mem_Icc] at hxR
    have hle : R ≤ R' := by rw [hR'def]; linarith [le_abs_self R]
    have hge : -R' ≤ -R := by rw [hR'def]; linarith [neg_abs_le R]
    exact ⟨le_trans hge hxR.1, le_trans hxR.2 hle⟩
  -- integrability of `|y|^{e−2c'}` on the symmetric interval (the iff)
  have hpow : IntegrableOn (fun y : ℝ => |y| ^ ((e : ℝ) - 2 * c')) (Icc (-R') R') volume := by
    rw [abs_rpow_integrableOn_Icc_symm _ _ hRpos]; linarith
  -- transfer to the divisor integrand off the null origin, then restrict to `Iy`
  have heq : (fun y : ℝ => |y| ^ ((e : ℝ) - 2 * c'))
      =ᵐ[volume.restrict (Icc (-R') R')] (fun y : ℝ => |y ^ 2| ^ (-c') * |y| ^ e) := by
    have hnull : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ 0 :=
      ae_iff.2 (by simpa using measure_singleton (0:ℝ))
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [hnull] with y hy _
    exact (boxpm_y_integrand_eq e c' hy).symm
  have hbig : IntegrableOn (fun y : ℝ => |y ^ 2| ^ (-c') * |y| ^ e) (Icc (-R') R') volume :=
    hpow.congr heq
  exact hbig.mono_set hsub

/-! ## 2. The box-integrability characterisation (the cover's per-chart object) -/

/-- **The box product-min, integrability form (GE leg — the finite-summand feed).** For `e = mk − 1`,
if `c' < (e+1)/2` (so the `y₀`-side box-integral over a bounded interval `Iy` is finite) and `|K|^{−c'}`
is integrable on the core box `Vz`, then the pulled-back integrand `|y₀²·K|^{−c'}·|y₀|^e` is integrable
on the rectangle `Iy ×ˢ Vz`. This is what the cover's `g5_flat_cover` finite-sum consumes:
`c' < min{(e+1)/2, rlctAtOn K 0}` ⟹ each chart summand finite. -/
theorem boxpm_integrableOn_of_lt (K : Z → ℝ) (hKm : Measurable K) (e : ℕ) (c' : ℝ) (hc' : 0 ≤ c')
    (Iy : Set ℝ) (hIy : MeasurableSet Iy) (hIybdd : Bornology.IsBounded Iy)
    (hc'lt : c' < ((e : ℝ) + 1) / 2)
    (Vz : Set Z) (hKint : IntegrableOn (fun z => |K z| ^ (-c')) Vz volume) :
    IntegrableOn (fun p : ℝ × Z => |p.1 ^ 2 * K p.2| ^ (-c') * |p.1| ^ e) (Iy ×ˢ Vz) volume := by
  -- the integrand is measurable and nonnegative; reduce to a finite lintegral.
  have hmeas : Measurable (fun p : ℝ × Z => |p.1 ^ 2 * K p.2| ^ (-c') * |p.1| ^ e) := by
    have : Measurable (fun p : ℝ × Z => p.1 ^ 2 * K p.2) :=
      (measurable_fst.pow_const 2).mul (hKm.comp measurable_snd)
    fun_prop
  have hnn : ∀ p : ℝ × Z, 0 ≤ |p.1 ^ 2 * K p.2| ^ (-c') * |p.1| ^ e :=
    fun p => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (by positivity)
  rw [IntegrableOn, Integrable, hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun p => hnn p))]
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  -- factorise the lintegral over the rectangle
  rw [boxpm_rect_split K hKm e c' Iy Vz]
  -- both factors finite ⟹ product finite
  apply ENNReal.mul_lt_top
  · -- `y₀`-side: integrable on bounded `Iy` ⟹ lintegral < ⊤
    have hyint := boxpm_y_integrableOn e c' hc'lt Iy hIy hIybdd
    have hynn : ∀ y : ℝ, 0 ≤ |y ^ 2| ^ (-c') * |y| ^ e :=
      fun y => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (by positivity)
    rw [IntegrableOn, Integrable, hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun y => hynn y))]
      at hyint
    exact hyint.2
  · -- core side: `hKint` ⟹ lintegral < ⊤
    have hKnn : ∀ z : Z, 0 ≤ |K z| ^ (-c') := fun z => Real.rpow_nonneg (abs_nonneg _) _
    rw [IntegrableOn, Integrable, hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun z => hKnn z))]
      at hKint
    exact hKint.2

end DLNFibre.DLN.RLCT
