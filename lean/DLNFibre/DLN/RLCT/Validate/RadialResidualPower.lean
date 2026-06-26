import DLNFibre.DLN.RLCT.Foundations.S1RadialMorse
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# `DLNFibre.DLN.RLCT.Validate.RadialResidualPower` — the residual-power Morse convolution atom (S2-FREE)

The genuinely-new finiteness atom for the rank-stratified hfin upper bound: the **residual-power**
generalisation of `radial_morse_dominates_lt_top`. The crude domination
`(∑Pᵢ² + w)^{−c'} ≤ (∑Pᵢ²)^{−c'}` caps a Morse-block peel at `c' < n/2`, discarding the core's
threshold — it cannot reach the genuine ADDITIVE disjoint-sum threshold. For a disjoint sum
`(‖T‖² ⊕ core)` whose total rlct is `n/2 + λ(core)` (e.g. the `(3,3,4)` cell `‖T‖² ⊕ ‖Δ·S‖²`,
`2 + 2 = 4`), the T-peel must leave a RESIDUAL POWER of the core that the core integral then absorbs at
the SHIFTED exponent `c'' = c' − n/2`:

    ∫_{[−T,T]ⁿ} (∑ᵢ Pᵢ² + w)^{−c'} dP  ≤  C · w^{−(c' − n/2)}     (w > 0, c' > n/2),

with `C = ∫_{ℝⁿ} (‖Q‖² + 1)^{−c'} dQ < ∞` (finite iff `c' > n/2`, by Mathlib
`integrable_rpow_neg_one_add_norm_sq`). Composing `w := core(z)` under the outer `z`-integral and
recursing on the core at `c''` reaches the additive threshold (pp-r1-genM-2 §Q1, decorrelated-Codex
confirmed; thread 28 `codex/convolution-additivity-answer.md`).

## S2-hygiene
S2-FREE: the only analytic input is `integrable_rpow_neg_one_add_norm_sq` (the Japanese-bracket
finiteness, `(1+‖x‖²)^{−r}` integrable for `finrank < r`) + the scaling `integral_comp_smul` on the
Haar `volume` of `EuclideanSpace` + the `PiLp.volume_preserving_toLp` transport. No `monomial_rlct`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Metric Module
open scoped ENNReal BigOperators

/-! ## The unit-core full-space constant `C = ∫_{ℝⁿ}(‖Q‖²+1)^{−c'}` -/

/-- **The unit-core constant** `Cresid n c' := ∫_{ℝⁿ}(‖Q‖² + 1)^{−c'} dQ` on `EuclideanSpace ℝ (Fin n)`
(the `w = 1` residual integral). Finite for `c' > n/2`; the `w`-independent constant the residual-power
bound pulls out. -/
noncomputable def Cresid (n : ℕ) (c' : ℝ) : ℝ :=
  ∫ Q : EuclideanSpace ℝ (Fin n), ((‖Q‖ ^ 2 + 1) ^ (-c'))

/-- `(‖Q‖² + 1)^{−c'}` is integrable on `EuclideanSpace ℝ (Fin n)` for `n/2 < c'` (Mathlib
`integrable_rpow_neg_one_add_norm_sq`, with `r = 2c'` so `finrank = n < 2c' ⟺ n/2 < c'`). -/
theorem integrable_core_unit (n : ℕ) (c' : ℝ) (hc' : (n : ℝ) / 2 < c') :
    Integrable (fun Q : EuclideanSpace ℝ (Fin n) => (‖Q‖ ^ 2 + 1) ^ (-c')) := by
  have hnr : (finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) < 2 * c' := by
    rw [finrank_euclideanSpace_fin]; linarith
  have h := integrable_rpow_neg_one_add_norm_sq
    (E := EuclideanSpace ℝ (Fin n)) (μ := volume) hnr
  -- `(1 + ‖x‖²)^(−(2c')/2) = (‖x‖² + 1)^(−c')`
  refine h.congr (Filter.Eventually.of_forall (fun Q => ?_))
  show (1 + ‖Q‖ ^ 2) ^ (-(2 * c') / 2) = (‖Q‖ ^ 2 + 1) ^ (-c')
  rw [add_comm (1 : ℝ) (‖Q‖ ^ 2), show (-(2 * c') / 2 : ℝ) = -c' by ring]

/-- `0 ≤ Cresid n c'` (the integrand is nonnegative). -/
theorem Cresid_nonneg (n : ℕ) (c' : ℝ) : 0 ≤ Cresid n c' := by
  unfold Cresid
  apply integral_nonneg
  intro Q
  exact Real.rpow_nonneg (by positivity) _

/-! ## The residual-power bound on `EuclideanSpace` (the Bochner-integral heart) -/

/-- **The full-space residual scaling (Bochner).** For `w > 0`, the full-space integral of
`(‖P‖² + w)^{−c'}` scales as `w^{n/2 − c'} · Cresid n c'`. Via the Haar scaling `integral_comp_smul`
with `R = √w`: `P = √w • Q` sends `‖P‖² + w = w·(‖Q‖² + 1)` and contributes `(√w)^{−n}` from the
Jacobian. -/
theorem integral_core_full_eq (n : ℕ) (c' : ℝ) (w : ℝ) (hw : 0 < w) :
    ∫ P : EuclideanSpace ℝ (Fin n), ((‖P‖ ^ 2 + w) ^ (-c'))
      = w ^ ((n : ℝ) / 2 - c') * Cresid n c' := by
  set g : EuclideanSpace ℝ (Fin n) → ℝ := fun P => (‖P‖ ^ 2 + w) ^ (-c') with hg
  set s : ℝ := Real.sqrt w with hs
  have hspos : 0 < s := Real.sqrt_pos.2 hw
  -- `integral_comp_smul`: ∫ g (s • Q) = |(s^n)⁻¹| • ∫ g
  have hcs := Measure.integral_comp_smul (volume : Measure (EuclideanSpace ℝ (Fin n))) g s
  rw [finrank_euclideanSpace_fin] at hcs
  -- the scaled integrand: g (s • Q) = w^{−c'} · (‖Q‖²+1)^{−c'}
  have hscaled : ∀ Q : EuclideanSpace ℝ (Fin n),
      g (s • Q) = w ^ (-c') * (‖Q‖ ^ 2 + 1) ^ (-c') := by
    intro Q
    have hnorm : ‖s • Q‖ ^ 2 = w * ‖Q‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos, mul_pow, hs, Real.sq_sqrt hw.le]
    simp only [hg]
    rw [hnorm, show w * ‖Q‖ ^ 2 + w = w * (‖Q‖ ^ 2 + 1) by ring,
      Real.mul_rpow hw.le (by positivity)]
  -- `∫ g (s•Q) dQ = w^{−c'} · Cresid`
  have hlhs : ∫ Q, g (s • Q) = w ^ (-c') * Cresid n c' := by
    simp_rw [hscaled]
    rw [integral_const_mul]
    rfl
  rw [hlhs] at hcs
  -- solve for `∫ g`: `w^{−c'}·Cresid = (s^n)⁻¹ • ∫ g`, so `∫ g = s^n · w^{−c'} · Cresid`
  rw [smul_eq_mul, abs_of_nonneg (by positivity)] at hcs
  -- `(s^n)⁻¹ ≠ 0`
  have hsn : (s ^ n)⁻¹ ≠ 0 := by positivity
  have : ∫ P, g P = s ^ n * (w ^ (-c') * Cresid n c') := by
    field_simp at hcs ⊢
    linarith [hcs]
  rw [this]
  -- `s^n = w^{n/2}` and `w^{n/2}·w^{−c'} = w^{n/2−c'}`
  have hsn2 : s ^ n = w ^ ((n : ℝ) / 2) := by
    rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_natCast (w ^ ((1 : ℝ) / 2)) n,
      ← Real.rpow_mul hw.le]
    congr 1
    ring
  rw [hsn2, ← mul_assoc, ← Real.rpow_add hw, show (n : ℝ) / 2 + -c' = (n : ℝ) / 2 - c' by ring]

/-- **The residual-power bound on the EuclideanSpace ball.** For `n/2 < c'`, `0 < w`, every `R`,
`∫_{ball 0 R} (‖P‖² + w)^{−c'} ≤ w^{−(c' − n/2)} · Cresid n c'` (bound the ball by the full space; the
integrand is nonneg and integrable). -/
theorem integrable_core_w (n : ℕ) (c' : ℝ) (hc' : (n : ℝ) / 2 < c') (w : ℝ) (hw : 0 < w) :
    Integrable (fun P : EuclideanSpace ℝ (Fin n) => (‖P‖ ^ 2 + w) ^ (-c')) := by
  -- `(‖P‖² + w)^{−c'} = w^{−c'}·(‖(√w)⁻¹·P‖² + 1)^{−c'}`, integrable by composing the unit-core
  -- integrability with the measure-preserving-up-to-scale dilation. Bound by const·unit-core instead.
  have hcore := integrable_core_unit n c' hc'
  -- pointwise `(‖P‖²+w)^{−c'} ≤ w^{−c'}` is false (decays); use the dilation comparison:
  -- `(‖P‖²+w)^{−c'} = w^{−c'}(‖P‖²/w+1)^{−c'}`. Compose `Q ↦ √w⁻¹•Q` (a homeomorph) with the unit core.
  set s : ℝ := Real.sqrt w with hs
  have hspos : 0 < s := Real.sqrt_pos.2 hw
  have hcomp : (fun P : EuclideanSpace ℝ (Fin n) => (‖P‖ ^ 2 + w) ^ (-c'))
      = fun P => w ^ (-c')
          * (fun Q : EuclideanSpace ℝ (Fin n) => (‖Q‖ ^ 2 + 1) ^ (-c')) (s⁻¹ • P) := by
    funext P
    have hnorm : ‖s⁻¹ • P‖ ^ 2 = w⁻¹ * ‖P‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), mul_pow,
        show (s⁻¹) ^ 2 = w⁻¹ by rw [hs, ← Real.sqrt_inv, Real.sq_sqrt (by positivity)]]
    simp only
    rw [hnorm, show w⁻¹ * ‖P‖ ^ 2 + 1 = w⁻¹ * (‖P‖ ^ 2 + w) by field_simp,
      Real.mul_rpow (by positivity) (by positivity),
      show (w⁻¹ : ℝ) ^ (-c') = w ^ c' by
        rw [Real.inv_rpow hw.le, Real.rpow_neg hw.le, inv_inv],
      ← mul_assoc, ← Real.rpow_add hw]
    norm_num
  rw [hcomp]
  exact ((hcore.comp_smul (R := s⁻¹) (by positivity)).const_mul (w ^ (-c')))

theorem integral_core_ball_le (n : ℕ) (c' : ℝ) (hc' : (n : ℝ) / 2 < c') (w : ℝ) (hw : 0 < w)
    (R : ℝ) :
    ∫ P in ball (0 : EuclideanSpace ℝ (Fin n)) R, ((‖P‖ ^ 2 + w) ^ (-c'))
      ≤ w ^ (-(c' - (n : ℝ) / 2)) * Cresid n c' := by
  refine le_trans (setIntegral_le_integral (integrable_core_w n c' hc' w hw)
    (Filter.Eventually.of_forall (fun P => Real.rpow_nonneg (by positivity) _))) ?_
  rw [integral_core_full_eq n c' w hw, show (-(c' - (n : ℝ) / 2)) = (n : ℝ) / 2 - c' by ring]

/-! ## The residual-power bound on the Morse box (the form the recursion consumes) -/

/-- **The residual-power Morse convolution bound (S2-FREE) — the new atom.** For an `n = m+1`-dim
Morse block `P : Fin (m+1) → ℝ` added to a strictly-positive core value `w > 0`, and `c'` ABOVE the
Morse threshold `(m+1)/2`, the box integral carries a RESIDUAL POWER `w^{−(c' − (m+1)/2)}` of the core:

    ∫_{[−T,T]^{m+1}} (∑ᵢ Pᵢ² + w)^{−c'} dP  ≤  ofReal( Cresid (m+1) c' · w^{−(c' − (m+1)/2)} ).

The disjoint-sum bridge the additive threshold needs: composing `w := core(z)` (measurable, `> 0` a.e.)
under the outer `z`-integral feeds the core at the SHIFTED exponent `c'' = c' − (m+1)/2`. The box is
enclosed in `ball 0 R` and transported to `EuclideanSpace` (`PiLp.volume_preserving_toLp`); the ball
bound is `integral_core_ball_le`. S2-FREE (built on `integrable_rpow_neg_one_add_norm_sq`). -/
theorem radial_morse_residual_power_le (m : ℕ) (c' : ℝ) (hc' : (m + 1 : ℝ) / 2 < c')
    (T : ℝ) (hT : 0 < T) (w : ℝ) (hw : 0 < w) :
    ∫⁻ P in morseBox (m + 1) T, ENNReal.ofReal ((∑ i, (P i) ^ 2 + w) ^ (-c'))
      ≤ ENNReal.ofReal (Cresid (m + 1) c' * w ^ (-(c' - (m + 1 : ℝ) / 2))) := by
  have hmp : MeasurePreserving (WithLp.toLp 2 : (Fin (m+1) → ℝ) → EuclideanSpace ℝ (Fin (m+1))) :=
    PiLp.volume_preserving_toLp (Fin (m+1))
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : (Fin (m+1) → ℝ) → EuclideanSpace ℝ (Fin (m+1))) :=
    (MeasurableEquiv.toLp 2 (Fin (m+1) → ℝ)).measurableEmbedding
  set R := Real.sqrt ((m+1) * T^2) + 1 with hRdef
  have hRpos : 0 < R := by positivity
  -- the box maps into ball 0 R (verbatim `sumSqND_box_lt_top`)
  have hsub : (WithLp.toLp 2 : (Fin (m+1) → ℝ) → EuclideanSpace ℝ (Fin (m+1))) ''
      morseBox (m+1) T ⊆ ball 0 R := by
    rintro y ⟨x, hx, rfl⟩
    simp only [morseBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] at hx
    rw [mem_ball_zero_iff, EuclideanSpace.norm_eq]
    have hb : ∀ i, (x i)^2 ≤ T^2 := fun i => by rcases hx i with ⟨h1, h2⟩; nlinarith
    calc Real.sqrt (∑ i, ‖x i‖^2) ≤ Real.sqrt (∑ i : Fin (m+1), T^2) := by
            apply Real.sqrt_le_sqrt; apply Finset.sum_le_sum; intro i _
            rw [Real.norm_eq_abs, sq_abs]; exact hb i
      _ = Real.sqrt ((m+1) * T^2) := by
            congr 1; rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast; ring
      _ < R := by rw [hRdef]; linarith [Real.sqrt_nonneg ((m+1) * T^2)]
  -- the integrand identity `(∑ Pᵢ² + w) = ‖toLp P‖² + w`
  have hnorm : ∀ x : Fin (m+1) → ℝ,
      (∑ i, (x i)^2 + w) = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (m+1)))‖ ^ 2 + w := by
    intro x
    congr 1
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    exact Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])
  -- transport the box-lintegral onto the EuclideanSpace ball, then bound by the Bochner ball-integral
  calc ∫⁻ P in morseBox (m+1) T, ENNReal.ofReal ((∑ i, (P i)^2 + w) ^ (-c'))
      = ∫⁻ P in morseBox (m+1) T,
          ENNReal.ofReal ((‖(WithLp.toLp 2 P : EuclideanSpace ℝ (Fin (m+1)))‖ ^ 2 + w) ^ (-c')) := by
        refine setLIntegral_congr_fun (morseBox_measurableSet _ _) (fun x _ => ?_)
        rw [hnorm x]
    _ = ∫⁻ y in (WithLp.toLp 2 : (Fin (m+1) → ℝ) → EuclideanSpace ℝ (Fin (m+1))) '' morseBox (m+1) T,
          ENNReal.ofReal ((‖y‖ ^ 2 + w) ^ (-c')) :=
        hmp.setLIntegral_comp_emb hemb
          (fun y => ENNReal.ofReal ((‖y‖ ^ 2 + w) ^ (-c'))) (morseBox (m+1) T)
    _ ≤ ∫⁻ y in ball (0 : EuclideanSpace ℝ (Fin (m+1))) R,
          ENNReal.ofReal ((‖y‖ ^ 2 + w) ^ (-c')) := lintegral_mono_set hsub
    _ = ENNReal.ofReal (∫ y in ball (0 : EuclideanSpace ℝ (Fin (m+1))) R, ((‖y‖ ^ 2 + w) ^ (-c'))) := by
        rw [← ofReal_integral_eq_lintegral_ofReal
          ((integrable_core_w (m+1) c' (by push_cast; linarith) w hw).restrict)
          (Filter.Eventually.of_forall (fun y => Real.rpow_nonneg (by positivity) _))]
    _ ≤ ENNReal.ofReal (w ^ (-(c' - (m + 1 : ℝ) / 2)) * Cresid (m+1) c') := by
        apply ENNReal.ofReal_le_ofReal
        have h := integral_core_ball_le (m+1) c' (by push_cast; linarith) w hw R
        rwa [show ((m + 1 : ℕ) : ℝ) / 2 = (m + 1 : ℝ) / 2 by push_cast; ring] at h
    _ = ENNReal.ofReal (Cresid (m + 1) c' * w ^ (-(c' - (m + 1 : ℝ) / 2))) := by
        rw [mul_comm]

end DLNFibre.DLN.RLCT
