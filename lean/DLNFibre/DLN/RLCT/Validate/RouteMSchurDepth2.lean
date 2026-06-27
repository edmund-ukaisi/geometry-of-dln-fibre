import DLNFibre.DLN.RLCT.Validate.RouteMSchur

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurDepth2` — the depth-2 recStep composition validator

The **depth-2 regression test** for the rank-stratified radial-Schur recursion (cert §4 N4,
`expeditions/2026-06-20-aoyagi-full/threads/28-hfin-recStep-spec/L32a-cover-cert.md`): the smallest
binding corank-2 case (`r = 2`, ONE nested minor-pivot level). It validates that the certified pieces —
N2b `schur_minorPivot_split` (the corank-`2`→corank-`1` Schur drop), the radial-blow-up homogeneity N1,
and the Morse terminal `radial_morse_dominates_lt_top` — **compose** into a finiteness proof, the way the
∀M N4 assembly needs.

Codex (xhigh, 2026-06-27, decorrelated) confirmed the design at `r = 2`: the `recStep` entry-chart cover
coincides with the max-modulus `1×1`-minor cover (a `1×1` minor IS a single entry), so depth-2 needs NO
genuinely-nested second cover; N2b (the comparison) is the right tool for the first drop, with N2a
(`rankOne_outerProduct_split`) the terminal rank-1 leaf. The certified design has no hole at `r = 2`.

## What this file delivers (the composition, S2-FREE)

* **`schurSplit_integrand_le`** — the pointwise integrand domination the recursion produces: on the
  N2b pivot cell, `frobSq (R·S)^{−c'} ≤ c₀^{−c'}·(frobSq (R·S)_top + frobSq (Sc·S_bot))^{−c'}` — the
  inverse-power flip of N2b's LOWER bound `c₀·D ≤ frobSq (R·S)`, zero-guarded by the UPPER bound.
* **`schurSplit_lintegral_le`** — its integral form: on any set where the N2b comparison holds
  pointwise, `∫_Z frobSq (R·S)^{−c'} ≤ c₀^{−c'} · ∫_Z D^{−c'}`. The corank-2 → split-form reduction.
* **`schurSplit_depth2_lt_top`** — the depth-2 composition CLOSED: chaining the reduction into the Morse
  terminal `radial_morse_dominates_lt_top`, the split-form `D = frobSq P + W z` (Morse block `P : Fin 4`
  ⊕ corank-1 residual `W ≥ 0`) integrates finitely for `c' < 2 = λ_{2,4}`. The N2b-split ⟶ Morse-leaf
  composition the ∀M N4 assembly rides, validated at the smallest binding corank-2 case.

The remaining cover-assembly (the radial-blow-up change-of-variables that turns the corank-2 core over
the matrix box into the split-form Morse coordinates `(P, z)` above, summed over the `r²` charts by
`recStep`) is the heavy N4 long pole, skeletoned in `RouteMSchur` (N4 `routeMCore_threshold_lt_top`).

## S2-hygiene
S2-FREE: the domination is the elementary inverse-power flip + N2b (itself S2-free). No `monomial_rlct`,
no new axiom.
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
theorem schurSplit_integrand_le {c₀ c₁ Dval F : ℝ} (hc₀ : 0 < c₀) (hD : 0 ≤ Dval) (hF : 0 ≤ F)
    (hlow : c₀ * Dval ≤ F) (hupp : F ≤ c₁ * Dval) (c' : ℝ) (hc' : 0 < c') :
    ENNReal.ofReal (F ^ (-c'))
      ≤ ENNReal.ofReal ((c₀ ^ (-c')) * (Dval ^ (-c'))) := by
  -- `c₀·D ≤ F`, both nonneg; the inverse power flips it, then split the constant out.
  have hcD : (0 : ℝ) ≤ c₀ * Dval := by positivity
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
          schurSplit_integrand_le hc₀ (hD z) (hF z) (hlow z) (hupp z) c' hc')
    _ = ∫⁻ z in Z, ENNReal.ofReal (c₀ ^ (-c')) * ENNReal.ofReal ((D z) ^ (-c')) ∂μ := by
        refine lintegral_congr (fun z => ?_)
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hc₀) _)]
    _ = ENNReal.ofReal (c₀ ^ (-c')) * ∫⁻ z in Z, ENNReal.ofReal ((D z) ^ (-c')) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-! ## The depth-2 composition CLOSED — N2b split ⟶ Morse terminal at the binding threshold

The recursion's terminal step at corank 2, made explicit: after the radial-blow-up change-of-variables
(the heavy N4 cover step, skeletoned in `RouteMSchur` N4) the corank-2 core integral becomes the
split-form integral over `(P, z)` — `P : Fin 4` the disjoint Morse block (the `j·p = 1·4 = 4` entries of
the top row `(R·S)_top`) and `W z ≥ 0` the corank-1 Schur residual `frobSq (Sc·S_bot)`. The N2b
comparison `c₀·(frobSq P + W z) ≤ frobSq (R·S) ≤ c₁·(frobSq P + W z)` then reduces it
(`schurSplit_lintegral_le`) to `∫ (frobSq P + W z)^{−c'}`, which the Morse terminal
`radial_morse_dominates_lt_top` closes for `c' < 4/2 = 2 = λ_{2,4}`. This validates that N2b's split feeds
the Morse leaf at exactly the binding threshold — the corank-2 → corank-1 → corank-0 chain composes. -/

/-- **The depth-2 composition, CLOSED (S2-FREE).** The split-form integral `∫_z ∫_P (frobSq P + W z)^{−c'}`
— the form the radial-blow-up CoV turns the corank-2 core into — is finite for `c' < 2 = λ_{2,4}`, with
`P : Fin 4` the top Morse block (`j·p = 1·4`) and `W ≥ 0` the corank-1 Schur residual. The N2b split
(`schur_minorPivot_split`) ⟶ Morse terminal (`radial_morse_dominates_lt_top`, `m+1 = 4`) composition the
∀M N4 assembly rides, validated at the smallest binding corank-2 case (Codex-confirmed: no hole at `r=2`).
`∑ⱼ (P j)²` (`P : Fin 4 → ℝ`) is the `Fin 4` Morse sum-of-squares modelling the flattened top row
`(R·S)_top`; the `radial_morse_dominates_lt_top` bound (`m+1 = 4`, threshold `2`) gives `< ⊤`. -/
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
