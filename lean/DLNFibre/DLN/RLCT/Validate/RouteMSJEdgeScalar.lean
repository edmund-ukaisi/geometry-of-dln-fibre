import DLNFibre.DLN.RLCT.Validate.RouteMSJEdgeAtoms
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.HaarToSphere

set_option linter.style.longLine false

/-!
# `RouteMSJEdgeScalar` — the scalar engine of the corank-one edge (satred's b=1-FreeBilinear peel)

Thread `genm-tideD-joint` (aoyagi-full Stage 2). The network-free SCALAR atoms the matrix→scalar edge
reduction (`edge_coupledBox_lt_top`, `RouteMSJEdgeAssembly`) consumes. Built on dbuild's kit
(`RouteMSJEdgeAtoms`: `radial1D_lintegral_lt_top`, `one_add_sigmaLog_le_rpow`). All `Mathlib`-only, reusable.

satred's scalar model (D-cert §3, `edge_2d_factor.py`): the 2-D coupled leaf
`H_p(w) = ∫_{[−1,1]²}(w+x²y²)^{−p}` factors via `u = xy` into a 1-D radial `∫(w+u²)^{−p}du = w^{1/2−p}·B`
times the σ-radial `∫|y|⁻¹dy = log(1/τ)` — so the analytic content is `[scaled radial] × [log] × [δ-fold]`,
NOT a monolithic 2-D singular integral. This module lands the SCALED RADIAL (the `w^{1/2−p}` pivot-energy
dependence).

## What lands here
* `scaledRadial1D_eq` — the `w`-scaling of dbuild's 1-D radial: for `w > 0`,
  `∫⁻ t, (w+t²)^{−p} = w^{1/2−p} · ∫⁻ s, (1+s²)^{−p}` (the substitution `t = √w·s`, Jacobian `√w`,
  homogeneity `w+t² = w(1+s²)`). The `w^{1/2−p}` factor is satred's pivot-energy dependence.
* `scaledRadial1D_lt_top` — its finiteness for `w > 0`, `p > 1/2` (the scaled radial factor is finite,
  the `1/2 < p` tail condition inherited from `radial1D_lintegral_lt_top`).
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Real
open scoped ENNReal

/-- **The `w`-scaled 1-D radial value.** For `w > 0`, substituting `t = √w·s` (Jacobian `√w`, and
`w + t² = w + w·s² = w(1+s²)`) gives `∫⁻ t, (w+t²)^{−p} = w^{1/2−p} · ∫⁻ s, (1+s²)^{−p}`. The `w^{1/2−p}`
factor is the pivot-energy dependence the edge reduction carries into the arity−1 comparator (satred §3). -/
theorem scaledRadial1D_eq {w p : ℝ} (hw : 0 < w) :
    ∫⁻ t : ℝ, ENNReal.ofReal ((w + t ^ 2) ^ (-p))
      = ENNReal.ofReal (w ^ (1 / 2 - p))
          * ∫⁻ s : ℝ, ENNReal.ofReal ((1 + s ^ 2) ^ (-p)) := by
  classical
  set a : ℝ := Real.sqrt w with ha
  have hapos : 0 < a := Real.sqrt_pos.mpr hw
  have hane : a ≠ 0 := ne_of_gt hapos
  have hasq : a ^ 2 = w := Real.sq_sqrt (le_of_lt hw)
  -- integrand
  set f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal ((w + t ^ 2) ^ (-p)) with hf
  have hcont : Continuous (fun t : ℝ => (w + t ^ 2) ^ (-p)) :=
    (by fun_prop : Continuous fun t : ℝ => w + t ^ 2).rpow_const
      (fun t => Or.inl (by positivity))
  have hfmeas : Measurable f := ENNReal.measurable_ofReal.comp hcont.measurable
  -- change of variables t = a • s via `Real.map_volume_mul_left`
  have hmap := Real.map_volume_mul_left (a := a) hane
  have hlm := lintegral_map (μ := (volume : Measure ℝ)) hfmeas (measurable_const_mul a)
  -- `∫⁻ s, f (a*s) = ∫⁻ t, f t ∂(map (a*·) volume) = ofReal|a⁻¹| * ∫⁻ t, f t`
  rw [hmap, lintegral_smul_measure] at hlm
  -- evaluate `f (a*s) = ofReal(w^{−p}) * ofReal((1+s²)^{−p})`
  have hinner : ∀ s : ℝ, f (a * s) = ENNReal.ofReal (w ^ (-p)) * ENNReal.ofReal ((1 + s ^ 2) ^ (-p)) := by
    intro s
    simp only [hf]
    have hstep : w + (a * s) ^ 2 = w * (1 + s ^ 2) := by
      rw [mul_pow, hasq]; ring
    rw [hstep, Real.mul_rpow (le_of_lt hw) (by positivity),
      ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hw) _)]
  -- so `∫⁻ s, f (a*s) = ofReal(w^{−p}) * radial`
  have hRHS : ∫⁻ s : ℝ, f (a * s)
      = ENNReal.ofReal (w ^ (-p)) * ∫⁻ s : ℝ, ENNReal.ofReal ((1 + s ^ 2) ^ (-p)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_congr hinner
  rw [hRHS] at hlm
  -- solve for `∫⁻ t, f t`: `ofReal|a⁻¹| * ∫⁻ f = ofReal(w^{−p}) * radial`
  -- multiply through by `ofReal|a| = ofReal a` (a > 0)
  have habs_inv : |a⁻¹| = a⁻¹ := abs_of_pos (inv_pos.mpr hapos)
  have hkey : ENNReal.ofReal a⁻¹ * (∫⁻ t : ℝ, f t)
      = ENNReal.ofReal (w ^ (-p)) * ∫⁻ s : ℝ, ENNReal.ofReal ((1 + s ^ 2) ^ (-p)) := by
    rw [habs_inv] at hlm; exact hlm.symm ▸ rfl
  -- ofReal a * ofReal a⁻¹ = 1
  have hcancel : ENNReal.ofReal a * ENNReal.ofReal a⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul (le_of_lt hapos), mul_inv_cancel₀ hane, ENNReal.ofReal_one]
  have hval : ∫⁻ t : ℝ, f t
      = ENNReal.ofReal a * (ENNReal.ofReal (w ^ (-p))
          * ∫⁻ s : ℝ, ENNReal.ofReal ((1 + s ^ 2) ^ (-p))) := by
    rw [← hkey, ← mul_assoc, hcancel, one_mul]
  -- assemble `ofReal a * ofReal(w^{−p}) = ofReal(w^{1/2−p})`
  have hpow : a * w ^ (-p) = w ^ (1 / 2 - p) := by
    rw [ha, Real.sqrt_eq_rpow, ← Real.rpow_add hw]; ring_nf
  rw [hval, ← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt hapos), hpow]

/-- **The scaled 1-D radial is finite** for `w > 0`, `p > 1/2`. Immediate from the scaling value
(`scaledRadial1D_eq`) and dbuild's `radial1D_lintegral_lt_top` (`∫⁻(1+s²)^{−p} < ⊤` at `p > 1/2`). -/
theorem scaledRadial1D_lt_top {w p : ℝ} (hw : 0 < w) (hp : 1 / 2 < p) :
    ∫⁻ t : ℝ, ENNReal.ofReal ((w + t ^ 2) ^ (-p)) < ⊤ := by
  rw [scaledRadial1D_eq hw]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (radial1D_lintegral_lt_top hp)

/-! ## The `a`-dimensional radial (JapaneseBracket) — the general-`a` corank leaf factor

The `b = 1` edge with `a`-dimensional corank (`Γ` an `a×1` column, `γ ∈ ℝ^a`) needs the `a`-dimensional
radial `∫_{ℝ^a}(w+‖x‖²)^{−p}` (the double-polar factor of the `‖γ‖²‖z‖²` model). Its finiteness is the
JapaneseBracket integrability `a < 2p`; its `w`-scaling supplies the `w^{a/2−p}` pivot-energy dependence. -/

/-- **The JapaneseBracket radial `∫_{ℝ^a}(1+‖x‖²)^{−p}` is finite** for `(a : ℝ) < 2p`. Pushes the
Mathlib Bochner integrability `integrable_rpow_neg_one_add_norm_sq` (`finrank < 2p`, and
`finrank (EuclideanSpace ℝ (Fin a)) = a`) to the `∫⁻ ofReal` finiteness via `ofReal ≤ ‖·‖ₑ`. The
`a`-generalisation of dbuild's `radial1D_lintegral_lt_top` (which is `a = 1`). -/
theorem japaneseBracket_euclid_lt_top {a : ℕ} {p : ℝ} (ha : (a : ℝ) < 2 * p) :
    ∫⁻ x : EuclideanSpace ℝ (Fin a), ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (-p)) < ⊤ := by
  have hr : (Module.finrank ℝ (EuclideanSpace ℝ (Fin a)) : ℝ) < 2 * p := by
    rw [finrank_euclideanSpace_fin]; exact ha
  have hint : Integrable (fun x : EuclideanSpace ℝ (Fin a) => ((1 : ℝ) + ‖x‖ ^ 2) ^ (-(2 * p) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq hr
  have hfun : (fun x : EuclideanSpace ℝ (Fin a) => ((1 : ℝ) + ‖x‖ ^ 2) ^ (-(2 * p) / 2))
      = (fun x : EuclideanSpace ℝ (Fin a) => (1 + ‖x‖ ^ 2) ^ (-p)) := by
    funext x; rw [show (-(2 * p) / 2) = -p from by ring]
  rw [hfun] at hint
  have hfin : ∫⁻ x : EuclideanSpace ℝ (Fin a), ‖(1 + ‖x‖ ^ 2) ^ (-p)‖ₑ < ⊤ := by
    rw [← hasFiniteIntegral_iff_enorm]; exact hint.hasFiniteIntegral
  refine lt_of_le_of_lt (lintegral_mono (fun x => ?_)) hfin
  exact Real.ofReal_le_enorm _

/-- **The `w`-scaled `a`-dimensional radial value.** For `w > 0`, substituting `x = √w • s`
(Jacobian `(√w)^a` via `map_addHaar_smul`, and `w + ‖x‖² = w + w‖s‖² = w(1+‖s‖²)`) gives
`∫_{ℝ^a}(w+‖x‖²)^{−p} = w^{a/2−p} · ∫_{ℝ^a}(1+‖s‖²)^{−p}`. The `w^{a/2−p}` factor is satred's
pivot-energy dependence for the general-`a` corank leaf. -/
theorem scaledRadialEuclid_eq {a : ℕ} {w p : ℝ} (hw : 0 < w) :
    ∫⁻ x : EuclideanSpace ℝ (Fin a), ENNReal.ofReal ((w + ‖x‖ ^ 2) ^ (-p))
      = ENNReal.ofReal (w ^ ((a : ℝ) / 2 - p))
          * ∫⁻ s : EuclideanSpace ℝ (Fin a), ENNReal.ofReal ((1 + ‖s‖ ^ 2) ^ (-p)) := by
  classical
  set c : ℝ := Real.sqrt w with hc
  have hcpos : 0 < c := Real.sqrt_pos.mpr hw
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hcsq : c ^ 2 = w := Real.sq_sqrt (le_of_lt hw)
  set f : EuclideanSpace ℝ (Fin a) → ℝ≥0∞ := fun x => ENNReal.ofReal ((w + ‖x‖ ^ 2) ^ (-p)) with hf
  have hfmeas : Measurable f := by
    apply ENNReal.measurable_ofReal.comp
    have hbase : Continuous (fun x : EuclideanSpace ℝ (Fin a) => w + ‖x‖ ^ 2) := by fun_prop
    exact (hbase.rpow_const (fun x => Or.inl (by positivity))).measurable
  -- change of variables x = c • s
  have hmap := MeasureTheory.Measure.map_addHaar_smul
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin a)))) hcne
  rw [finrank_euclideanSpace_fin] at hmap
  have hlm := lintegral_map (μ := (volume : Measure (EuclideanSpace ℝ (Fin a)))) hfmeas
    (measurable_const_smul c)
  rw [hmap, lintegral_smul_measure] at hlm
  -- evaluate `f (c • s)`
  have hinner : ∀ s : EuclideanSpace ℝ (Fin a),
      f (c • s) = ENNReal.ofReal (w ^ (-p)) * ENNReal.ofReal ((1 + ‖s‖ ^ 2) ^ (-p)) := by
    intro s
    simp only [hf]
    have hnorm : ‖c • s‖ ^ 2 = w * ‖s‖ ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hcsq]
    have hstep : w + ‖c • s‖ ^ 2 = w * (1 + ‖s‖ ^ 2) := by rw [hnorm]; ring
    rw [hstep, Real.mul_rpow (le_of_lt hw) (by positivity),
      ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hw) _)]
  have hRHS : ∫⁻ s : EuclideanSpace ℝ (Fin a), f (c • s)
      = ENNReal.ofReal (w ^ (-p)) * ∫⁻ s : EuclideanSpace ℝ (Fin a), ENNReal.ofReal ((1 + ‖s‖ ^ 2) ^ (-p)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_congr hinner
  rw [hRHS] at hlm
  -- `hlm : ofReal(w^{−p})·∫s = ofReal(|(c^a)⁻¹|)·∫f`; normalise to `(ofReal(c^a))⁻¹·∫f`
  have hcapos : 0 < c ^ a := pow_pos hcpos a
  have hcne0 : ENNReal.ofReal (c ^ a) ≠ 0 := (ENNReal.ofReal_pos.mpr hcapos).ne'
  rw [abs_of_pos (inv_pos.mpr hcapos), ENNReal.ofReal_inv_of_pos hcapos, smul_eq_mul] at hlm
  -- `c^a · w^{−p} = w^{a/2−p}`
  have hpow : ENNReal.ofReal (c ^ a) * ENNReal.ofReal (w ^ (-p)) = ENNReal.ofReal (w ^ ((a : ℝ) / 2 - p)) := by
    rw [← ENNReal.ofReal_mul (le_of_lt hcapos)]
    congr 1
    have hca : c ^ a = w ^ ((a : ℝ) / 2) := by
      rw [← Real.rpow_natCast c a, hc, Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hw)]
      congr 1; ring
    rw [hca, ← Real.rpow_add hw, sub_eq_add_neg]
  -- `∫f = ofReal(c^a) · (ofReal(w^{−p}) · ∫s)` by cancelling `(ofReal(c^a))⁻¹` against `hlm`
  have hval : ENNReal.ofReal (c ^ a) * (ENNReal.ofReal (w ^ (-p))
        * ∫⁻ s : EuclideanSpace ℝ (Fin a), ENNReal.ofReal ((1 + ‖s‖ ^ 2) ^ (-p)))
      = ∫⁻ x : EuclideanSpace ℝ (Fin a), f x :=
    calc ENNReal.ofReal (c ^ a) * (ENNReal.ofReal (w ^ (-p))
          * ∫⁻ s : EuclideanSpace ℝ (Fin a), ENNReal.ofReal ((1 + ‖s‖ ^ 2) ^ (-p)))
        = ENNReal.ofReal (c ^ a) * ((ENNReal.ofReal (c ^ a))⁻¹
            * ∫⁻ x : EuclideanSpace ℝ (Fin a), f x) :=
          congrArg (fun t => ENNReal.ofReal (c ^ a) * t) hlm.symm
      _ = (ENNReal.ofReal (c ^ a) * (ENNReal.ofReal (c ^ a))⁻¹)
            * ∫⁻ x : EuclideanSpace ℝ (Fin a), f x := by rw [← mul_assoc]
      _ = ∫⁻ x : EuclideanSpace ℝ (Fin a), f x := by
          rw [ENNReal.mul_inv_cancel hcne0 ENNReal.ofReal_ne_top, one_mul]
  exact hval.symm.trans (by rw [← mul_assoc, hpow])

/-- **The `w`-scaled `a`-dimensional radial is finite** for `w > 0`, `(a : ℝ) < 2p`. From the scaling
value (`scaledRadialEuclid_eq`) and the JapaneseBracket finiteness (`japaneseBracket_euclid_lt_top`). -/
theorem scaledRadialEuclid_lt_top {a : ℕ} {w p : ℝ} (hw : 0 < w) (ha : (a : ℝ) < 2 * p) :
    ∫⁻ x : EuclideanSpace ℝ (Fin a), ENNReal.ofReal ((w + ‖x‖ ^ 2) ^ (-p)) < ⊤ := by
  rw [scaledRadialEuclid_eq hw]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (japaneseBracket_euclid_lt_top ha)

end DLNFibre.DLN.RLCT
