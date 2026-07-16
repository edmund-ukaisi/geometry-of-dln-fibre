import DLNFibre.DLN.RLCT.Validate.RadialResidualPower

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RadialCriticalPower` — the critical/sub-critical residual-power atom (S2-FREE)

The companion of `radial_morse_residual_power_le` for the **`2q ≤ ub` side** of the interior `+ub`
residual-power chaining (couplerad §w3-boundary, R3/R4 regimes ①②). Where `radial_morse_residual_power_le`
handles the STRICTLY-supercritical exponent `c' > (m+1)/2` (regime ③, `2q > ub`), this atom handles the
critical and sub-critical `c' ≤ (m+1)/2` (regimes ①②, `2q ≤ ub`) — including the boundary `c' = (m+1)/2`
(`2q = ub`) where the pure box integral diverges *logarithmically*.

The device that folds every `c' ≤ (m+1)/2` cell into a residual-power bound with an **arbitrary small**
exponent `ε > 0`: split `−c' = −ε + (−(c'−ε))` and dominate

    (‖P‖² + w)^{−c'} = (‖P‖² + w)^{−ε} · (‖P‖² + w)^{−(c'−ε)}
                     ≤ w^{−ε} · ‖P‖^{−2(c'−ε)}          (a.e., `P ≠ 0`),

using `(‖P‖²+w)^{−ε} ≤ w^{−ε}` and `(‖P‖²+w)^{−(c'−ε)} ≤ (‖P‖²)^{−(c'−ε)}` (both `Real.rpow_le_rpow_of_nonpos`,
`0 ≤ c'−ε`). The residual `w^{−ε}` carries the same shape as regime ③'s `w^{−(c'−(m+1)/2)}`, but with `ε`
as small as we like — so the boundary log is never touched pointwise; it is absorbed by choosing `ε` below
the deep sub-chain threshold `½·minAdm(![u+a,u,d])`. The `P`-independent constant is the ball integral
`∫_{ball_R} ‖P‖^{−2(c'−ε)}`, finite because `c'−ε < (m+1)/2` (`euclidND_ball_integrable`).

S2-FREE: the only analytic input is `euclidND_ball_integrable` (⟵ `radial_ball_iff` ⟵ Mathlib
`integrable_fun_norm_addHaar`) + elementary `rpow` monotonicity. No `monomial_rlct`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Metric Module
open scoped ENNReal BigOperators

/-- **The `P`-independent ball constant** `critBallConst m s R := ∫_{ball_R ⊆ ℝ^{m+1}} ‖P‖^{−s}`, the
sub-critical companion of `Cresid`. Finite for `s < m+1` (i.e. the shifted exponent `2(c'−ε)`, with
`c'−ε < (m+1)/2`); the `w`-independent constant the critical residual-power bound pulls out. -/
noncomputable def critBallConst (m : ℕ) (s R : ℝ) : ℝ :=
  ∫ P : EuclideanSpace ℝ (Fin (m + 1)) in ball 0 R, ‖P‖ ^ (-s)

/-- `0 ≤ critBallConst m s R` (the integrand `‖P‖^{−s}` is nonnegative). -/
theorem critBallConst_nonneg (m : ℕ) (s R : ℝ) : 0 ≤ critBallConst m s R := by
  unfold critBallConst
  exact integral_nonneg (fun P => Real.rpow_nonneg (norm_nonneg _) _)

/-- **The critical/sub-critical residual-power bound on a ball (S2-FREE).** For `c' ≤ (m+1)/2` (the
`2q ≤ ub` regime, `c' = q`) and any residual exponent `ε` with `0 < ε ≤ c'` and `c' − ε < (m+1)/2`, the
ball integral carries the residual power `w^{−ε}` of the core `w > 0`:

    ∫⁻_{ball_R} (‖P‖² + w)^{−c'} dP  ≤  ofReal( w^{−ε} · critBallConst m (2(c'−ε)) R ).

The pointwise a.e. domination `(‖P‖²+w)^{−c'} ≤ w^{−ε}·‖P‖^{−2(c'−ε)}` (`Real.rpow_le_rpow_of_nonpos`
twice; fails only at `P = 0`, null), then the constant `∫_{ball_R} ‖P‖^{−2(c'−ε)}` finite via
`euclidND_ball_integrable` (`c'−ε < (m+1)/2`). -/
theorem lintegral_ball_critical_le (m : ℕ) (c' : ℝ) (R : ℝ) (hR : 0 < R)
    (w : ℝ) (hw : 0 < w) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ c') (hcrit : c' - ε < (m + 1 : ℝ) / 2) :
    ∫⁻ P in ball (0 : EuclideanSpace ℝ (Fin (m + 1))) R,
        ENNReal.ofReal ((‖P‖ ^ 2 + w) ^ (-c'))
      ≤ ENNReal.ofReal (w ^ (-ε) * critBallConst m (2 * (c' - ε)) R) := by
  -- integrability of the constant integrand `‖P‖^{−2(c'−ε)}` on the ball
  have hcε : c' - ε < (m + 1 : ℝ) / 2 := hcrit
  have hint : IntegrableOn (fun P : EuclideanSpace ℝ (Fin (m + 1)) => ‖P‖ ^ (-(2 * (c' - ε))))
      (ball 0 R) volume := euclidND_ball_integrable m R hR (c' - ε) hcε
  -- the pointwise a.e. domination (fails only at `P = 0`, which is null)
  have hae : (fun P : EuclideanSpace ℝ (Fin (m + 1)) => ENNReal.ofReal ((‖P‖ ^ 2 + w) ^ (-c')))
      ≤ᵐ[volume.restrict (ball 0 R)]
      (fun P => ENNReal.ofReal (w ^ (-ε) * ‖P‖ ^ (-(2 * (c' - ε))))) := by
    refine ae_restrict_of_ae ?_
    have h0 : ∀ᵐ P ∂(volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))),
        P ≠ (0 : EuclideanSpace ℝ (Fin (m + 1))) := by
      rw [ae_iff]
      simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
      exact measure_singleton 0
    filter_upwards [h0] with P hP
    apply ENNReal.ofReal_le_ofReal
    have hnpos : 0 < ‖P‖ := norm_pos_iff.mpr hP
    have hbw : 0 < ‖P‖ ^ 2 + w := by positivity
    have hsq : 0 < ‖P‖ ^ 2 := by positivity
    rw [show (-c') = (-ε) + (-(c' - ε)) by ring, Real.rpow_add hbw]
    have h1 : (‖P‖ ^ 2 + w) ^ (-ε) ≤ w ^ (-ε) :=
      Real.rpow_le_rpow_of_nonpos hw (by nlinarith) (by linarith)
    have h2 : (‖P‖ ^ 2 + w) ^ (-(c' - ε)) ≤ (‖P‖ ^ 2) ^ (-(c' - ε)) :=
      Real.rpow_le_rpow_of_nonpos hsq (by linarith) (by linarith)
    have h2' : (‖P‖ ^ 2) ^ (-(c' - ε)) = ‖P‖ ^ (-(2 * (c' - ε))) := by
      rw [← Real.rpow_natCast ‖P‖ 2, ← Real.rpow_mul (norm_nonneg _)]
      congr 1; push_cast; ring
    calc (‖P‖ ^ 2 + w) ^ (-ε) * (‖P‖ ^ 2 + w) ^ (-(c' - ε))
        ≤ w ^ (-ε) * (‖P‖ ^ 2) ^ (-(c' - ε)) :=
          mul_le_mul h1 h2 (Real.rpow_nonneg hbw.le _) (Real.rpow_nonneg hw.le _)
      _ = w ^ (-ε) * ‖P‖ ^ (-(2 * (c' - ε))) := by rw [h2']
  calc ∫⁻ P in ball (0 : EuclideanSpace ℝ (Fin (m + 1))) R,
          ENNReal.ofReal ((‖P‖ ^ 2 + w) ^ (-c'))
      ≤ ∫⁻ P in ball (0 : EuclideanSpace ℝ (Fin (m + 1))) R,
          ENNReal.ofReal (w ^ (-ε) * ‖P‖ ^ (-(2 * (c' - ε)))) := lintegral_mono_ae hae
    _ = ∫⁻ P in ball (0 : EuclideanSpace ℝ (Fin (m + 1))) R,
          ENNReal.ofReal (w ^ (-ε)) * ENNReal.ofReal (‖P‖ ^ (-(2 * (c' - ε)))) := by
        refine lintegral_congr_ae (Filter.Eventually.of_forall (fun P => ?_))
        change ENNReal.ofReal (w ^ (-ε) * ‖P‖ ^ (-(2 * (c' - ε))))
            = ENNReal.ofReal (w ^ (-ε)) * ENNReal.ofReal (‖P‖ ^ (-(2 * (c' - ε))))
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hw.le _)]
    _ = ENNReal.ofReal (w ^ (-ε)) * ∫⁻ P in ball (0 : EuclideanSpace ℝ (Fin (m + 1))) R,
          ENNReal.ofReal (‖P‖ ^ (-(2 * (c' - ε)))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (w ^ (-ε)) * ENNReal.ofReal (critBallConst m (2 * (c' - ε)) R) := by
        rw [critBallConst,
          ← ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall (fun P => Real.rpow_nonneg (norm_nonneg _) _))]
    _ = ENNReal.ofReal (w ^ (-ε) * critBallConst m (2 * (c' - ε)) R) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hw.le _)]

/-! ## The box form (the drop-in sibling of `radial_morse_residual_power_le`) -/

/-- **The critical/sub-critical residual-power Morse convolution bound on the box (S2-FREE).** The
`2q ≤ ub` companion of `radial_morse_residual_power_le` (which handles `2q > ub`), UNIFYING regimes ①②③
of couplerad §w3-boundary through the residual-exponent parameter `ε`: for a Morse block
`P : Fin (m+1) → ℝ` added to a strictly-positive core `w > 0`, ANY `c'`, and any `ε` with `0 < ε ≤ c'`
and `c' − ε < (m+1)/2`,

    ∫_{[−T,T]^{m+1}} (∑ᵢ Pᵢ² + w)^{−c'} dP  ≤  ofReal( w^{−ε} · critBallConst m (2(c'−ε)) R ),
    R = √((m+1)·T²) + 1.

The box is enclosed in `ball 0 R` and transported to `EuclideanSpace` (`PiLp.volume_preserving_toLp`,
verbatim `radial_morse_residual_power_le`); the ball bound is `lintegral_ball_critical_le`. The `ε` folds
the boundary log (`c' = (m+1)/2`) into a residual power `w^{−ε}` with `ε` as small as the deep sub-chain
threshold `½·minAdm(![u+a,u,d])` allows — the ε-window `(max(0, c'−(m+1)/2), min(c', ½minAdm(![u+a,u,d])))`
is nonempty exactly when `2c' < ub + minAdm(![u+a,u,d])` (corankrec's QIP `minAdm_le_inf_pivot_qip`). -/
theorem radial_morse_critical_power_le (m : ℕ) (c' : ℝ) (T : ℝ) (hT : 0 < T)
    (w : ℝ) (hw : 0 < w) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ c') (hcrit : c' - ε < (m + 1 : ℝ) / 2) :
    ∫⁻ P in morseBox (m + 1) T, ENNReal.ofReal ((∑ i, (P i) ^ 2 + w) ^ (-c'))
      ≤ ENNReal.ofReal (w ^ (-ε) *
          critBallConst m (2 * (c' - ε)) (Real.sqrt ((m + 1) * T ^ 2) + 1)) := by
  have hmp : MeasurePreserving (WithLp.toLp 2 : (Fin (m+1) → ℝ) → EuclideanSpace ℝ (Fin (m+1))) :=
    PiLp.volume_preserving_toLp (Fin (m+1))
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : (Fin (m+1) → ℝ) → EuclideanSpace ℝ (Fin (m+1))) :=
    (MeasurableEquiv.toLp 2 (Fin (m+1) → ℝ)).measurableEmbedding
  set R := Real.sqrt ((m+1) * T^2) + 1 with hRdef
  have hRpos : 0 < R := by positivity
  -- the box maps into ball 0 R (verbatim `radial_morse_residual_power_le`)
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
    _ ≤ ENNReal.ofReal (w ^ (-ε) * critBallConst m (2 * (c' - ε)) R) :=
        lintegral_ball_critical_le m c' R hRpos w hw ε hε hεle hcrit

end DLNFibre.DLN.RLCT
