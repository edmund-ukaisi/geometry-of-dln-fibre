import DLNFibre.DLN.RLCT.Validate.RouteMSchur

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurDepth2` — the corank-2 N2b→Morse reduction END-PIECES

The two ends of the rank-stratified radial-Schur recursion (cert §4 N4,
`expeditions/2026-06-20-aoyagi-full/threads/28-hfin-recStep-spec/L32a-cover-cert.md`) at the smallest
binding corank-2 case (`r = 2`, ONE nested minor-pivot level): (i) the N2b-shaped inverse-power reduction
that replaces a core `F` two-sided-comparable to a split form `D` by `D^{−c'}`, and (ii) the finiteness of
the `Fin 4` Morse terminal for `c' < 2 = λ_{2,4}`. These are the INGREDIENTS the depth-2 recursion needs;
they are **three separate lemmas, NOT chained end-to-end** — the missing weld is the radial-blow-up
change-of-variables that turns the corank-2 core `∫_R frobSq (R·S)^{−c'}` over the matrix box INTO the
split form, which stays the deferred N4 long pole (`RouteMSchur` N4 `routeMCore_threshold_lt_top`).

Codex (xhigh, 2026-06-27, decorrelated) confirmed the design at `r = 2`: the `recStep` entry-chart cover
coincides with the max-modulus `1×1`-minor cover (a `1×1` minor IS a single entry), so depth-2 needs NO
genuinely-nested second cover; N2b (the comparison) is the right tool for the first drop, with N2a
(`rankOne_outerProduct_split`) the terminal rank-1 leaf. The certified design has no hole at `r = 2`.

## What this file delivers (the two reduction ends, S2-FREE — NOT their composition)

* **`schurSplit_integrand_le`** — the pointwise inverse-power flip: for reals `c₀·D ≤ F ≤ c₁·D` (the N2b
  comparison shape; `D, F` abstract reals, NO matrix), `ofReal (F^{−c'}) ≤ ofReal (c₀^{−c'}·D^{−c'})`.
  The flip of the LOWER bound, zero-guarded by the UPPER bound. Takes the comparison as a HYPOTHESIS — it
  does not invoke N2b (`schur_minorPivot_split`) to produce it.
* **`schurSplit_lintegral_le`** — its integral form: on a set where `c₀·D z ≤ F z ≤ c₁·D z` holds
  pointwise (abstract `D, F : Ω → ℝ`), `∫_Z F^{−c'} ≤ c₀^{−c'} · ∫_Z D^{−c'}`. The core → split-form
  reduction, given the comparison.
* **`schurSplit_depth2_lt_top`** — the Morse-terminal END: the split-form integral
  `∫_z ∫_P (∑ⱼ (P j)² + W z)^{−c'}` (`P : Fin 4` a FREE Morse block, `W ≥ 0` an arbitrary residual)
  is finite for `c' < 2 = λ_{2,4}`. This is `radial_morse_dominates_lt_top` at `m+1 = 4`; it takes the
  split form as its STARTING point (it does NOT start from the corank-2 core, and does NOT consume the two
  reduction lemmas above). The core → split-form weld (the radial-blow-up CoV) is the deferred N4 step.

## S2-hygiene
S2-FREE: the reduction is the elementary inverse-power flip; the terminal is `radial_ball_iff`-based. No
`monomial_rlct`, no new axiom.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

/-! ## The N2b-derived integrand domination (the corank-2 → split-form recursion step)

N2b gives the two-sided uniform comparison `c₀·D ≤ frobSq (R·S) ≤ c₁·D`, where
`D = frobSq (R·S)_top + frobSq (Sc·S_bot)` is the disjoint Morse-block-⊕-corank-1-residual split.
For the upper-bound finiteness only the LOWER side `c₀·D ≤ frobSq (R·S)` is needed: the inverse power
flips it (antitone for `−c' ≤ 0`) to `frobSq (R·S)^{−c'} ≤ c₀^{−c'}·D^{−c'}`, with the zero-guard
`D = 0 → frobSq (R·S) = 0` from `c₀ > 0`. Integrating, the corank-2 core integral is dominated by the
split-form integral — the recursion's reduction to the Morse leaf + the corank-1 residual. -/

/-- **The inverse-power flip of N2b's comparison (the recursion's integrand step).** On the N2b pivot
cell, the corank-2 core integrand is dominated by the split-form integrand: with `D` the disjoint
Morse-block-⊕-Schur-residual sum, `ofReal (F^{−c'}) ≤ ofReal (c₀^{−c'}·D^{−c'})` for `F = frobSq (R·S)`.
The inverse-power antitone flip of N2b's LOWER bound `c₀·D ≤ F`; the zero-guard `c₀·D = 0 → F = 0` is
supplied by N2b's UPPER bound `F ≤ c₁·D` (so `D = 0 ⟹ F = 0`). Both sides of the two-sided N2b
comparison are load-bearing: the lower for the bound, the upper for the guard. The pointwise reduction
the per-chart cover consumes. -/
theorem schurSplit_integrand_le {c₀ c₁ Dval F : ℝ} (hc₀ : 0 < c₀) (hD : 0 ≤ Dval)
    (hlow : c₀ * Dval ≤ F) (hupp : F ≤ c₁ * Dval) (c' : ℝ) (hc' : 0 < c') :
    ENNReal.ofReal (F ^ (-c'))
      ≤ ENNReal.ofReal ((c₀ ^ (-c')) * (Dval ^ (-c'))) := by
  -- `c₀·D ≤ F`, both nonneg; the inverse power flips it, then split the constant out.
  have hcD : (0 : ℝ) ≤ c₀ * Dval := by positivity
  have hF : (0 : ℝ) ≤ F := le_trans hcD hlow
  have hsplit : (c₀ * Dval) ^ (-c') = (c₀ ^ (-c')) * (Dval ^ (-c')) :=
    Real.mul_rpow (le_of_lt hc₀) hD
  rw [← hsplit]
  -- inverse-power antitone flip of `c₀·D ≤ F`, zero-guarded by the upper bound (`D = 0 ⟹ F = 0`)
  rcases eq_or_lt_of_le hcD with hcD0 | hcD0
  · -- c₀·D = 0 ⟹ D = 0 (c₀ > 0) ⟹ F ≤ c₁·D = 0 (upper bound), F ≥ 0 ⟹ F = 0; both sides ofReal 0.
    have hD0 : Dval = 0 := by
      rcases mul_eq_zero.1 hcD0.symm with h' | h'
      · exact absurd h' (ne_of_gt hc₀)
      · exact h'
    have hF0 : F = 0 := le_antisymm (by rw [hD0, mul_zero] at hupp; exact hupp) hF
    rw [hF0, ← hcD0]
  · -- 0 < c₀·D ≤ F: base-antitone for the nonpositive exponent
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hcD0 hlow (by linarith))

/-- **The integral form (the per-set recursion reduction).** On a measurable set `Z` where N2b's
two-sided comparison `c₀·D z ≤ F z ≤ c₁·D z` holds pointwise (uniform `c₀, c₁ > 0`), the corank-2 core
integral is dominated by the split-form integral: `∫_Z F^{−c'} ≤ ofReal (c₀^{−c'}) · ∫_Z D^{−c'}`. The
pointwise `schurSplit_integrand_le` under the integral, then `lintegral_const_mul'` pulls the
`Z`-independent constant `c₀^{−c'}` out. This is the recursion's reduction of the corank-2 leaf to the
split form `D` (a Morse block ⊕ the corank-1 Schur residual) — the form the next level / the Morse
terminal consumes. Abstract over an arbitrary measure space (the `R`- or `(R,S)`-domain). -/
theorem schurSplit_lintegral_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (D F : Ω → ℝ) (Z : Set Ω)
    (hD : ∀ z, 0 ≤ D z) (hF : ∀ z, 0 ≤ F z)
    (hlow : ∀ z, c₀ * D z ≤ F z) (hupp : ∀ z, F z ≤ c₁ * D z)
    (c' : ℝ) (hc' : 0 < c') :
    (∫⁻ z in Z, ENNReal.ofReal ((F z) ^ (-c')) ∂μ)
      ≤ ENNReal.ofReal (c₀ ^ (-c')) * ∫⁻ z in Z, ENNReal.ofReal ((D z) ^ (-c')) ∂μ := by
  calc (∫⁻ z in Z, ENNReal.ofReal ((F z) ^ (-c')) ∂μ)
      ≤ ∫⁻ z in Z, ENNReal.ofReal ((c₀ ^ (-c')) * ((D z) ^ (-c'))) ∂μ :=
        lintegral_mono (fun z =>
          schurSplit_integrand_le hc₀ (hD z) (hlow z) (hupp z) c' hc')
    _ = ∫⁻ z in Z, ENNReal.ofReal (c₀ ^ (-c')) * ENNReal.ofReal ((D z) ^ (-c')) ∂μ := by
        refine lintegral_congr (fun z => ?_)
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hc₀) _)]
    _ = ENNReal.ofReal (c₀ ^ (-c')) * ∫⁻ z in Z, ENNReal.ofReal ((D z) ^ (-c')) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-! ## The Morse-terminal END — the split-form integral at the binding corank-2 threshold

The terminal of the corank-2 recursion, on the split form the N4 radial-blow-up CoV produces (that CoV
is the deferred weld — this lemma takes the split form as GIVEN, it does not derive it from the core).
`P : Fin 4` is the disjoint Morse block (the `j·p = 1·4 = 4` entries of the top row `(R·S)_top`),
`W z ≥ 0` an arbitrary residual standing for the corank-1 Schur core `frobSq (Sc·S_bot)`. The split-form
integral `∫_z ∫_P (∑ⱼ (P j)² + W z)^{−c'}` is `radial_morse_dominates_lt_top` at `m+1 = 4`, finite for
`c' < 4/2 = 2 = λ_{2,4}` — the binding corank-2 threshold (cf. `core334_lt_top`, also `c'' < 2`). -/

/-- **The Morse-terminal finiteness at the corank-2 threshold (S2-FREE).** The split-form integral
`∫_z ∫_P (∑ⱼ (P j)² + W z)^{−c'}` is finite for `c' < 2 = λ_{2,4}`, with `P : Fin 4` a FREE Morse block
(modelling the flattened top row `(R·S)_top`, `j·p = 1·4`) and `W ≥ 0` an arbitrary residual (standing
for the corank-1 Schur core `frobSq (Sc·S_bot)`). This is `radial_morse_dominates_lt_top` at `m+1 = 4`,
the END of the corank-2 N2b→Morse reduction. It takes the split form as its STARTING point — the core →
split-form weld (the radial-blow-up CoV, summed over the `r²` charts by `recStep`) is the deferred N4
step (`RouteMSchur` N4); this lemma does NOT consume `schurSplit_lintegral_le` / `schur_minorPivot_split`.
The threshold `2 = (m+1)/2` is binding (Codex-confirmed: the certified recursion has no hole at `r=2`). -/
theorem schurSplit_depth2_lt_top {k : ℕ} (c' : ℝ) (hc0 : 0 ≤ c') (hc' : c' < 2)
    (T : ℝ) (hT : 0 < T) (W : (Fin k → ℝ) → ℝ) (hWnn : ∀ z, 0 ≤ W z) (hWmeas : Measurable W) :
    ∫⁻ z in morseBox k T, ∫⁻ P in morseBox 4 T,
        ENNReal.ofReal ((∑ j, (P j) ^ 2 + W z) ^ (-c')) < ⊤ := by
  -- the Morse block is `Fin 4 = Fin (3+1)`; the threshold `c' < (3+1)/2 = 2 = λ_{2,4}` binds.
  have hmorse := radial_morse_dominates_lt_top (m := 3) (k := k) c'
    (by norm_num; linarith) hc0 T hT W hWnn hWmeas
  exact lt_of_le_of_lt hmorse
    (ENNReal.mul_lt_top (Kbound_lt_top 3 T hT c' (by norm_num; linarith)) (morseBox_volume_lt_top k T))

end DLNFibre.DLN.RLCT
