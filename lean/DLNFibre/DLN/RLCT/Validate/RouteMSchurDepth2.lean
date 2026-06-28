import DLNFibre.DLN.RLCT.Validate.RouteMSchur

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurDepth2` — the corank-2 N2b→Morse weld (inner-S CLOSED)

The depth-2 weld of the rank-stratified radial-Schur recursion (cert §4 N4,
`expeditions/2026-06-20-aoyagi-full/threads/28-hfin-recStep-spec/L32a-cover-cert.md`) at the smallest
binding corank-2 case (`r = 2`, ONE nested minor-pivot level). Two halves:

* the abstract reduction ends — the N2b-shaped inverse-power reduction (core `F` ≍ split form `D` ⟹
  `F^{−c'} ≤ c₀^{−c'}·D^{−c'}`) + the `Fin 4` Morse terminal for `c' < 2 = λ_{2,4}`;
* **the INNER-S weld CHAINED (`schurInner_S_le`, PROVED end-to-end)** — on a fixed radial-blow-up angular
  chart (`R 0 0 = 1`, `|R i k| ≤ 1`), `∫_{S ∈ matBox 2 4 T} frobSq (R·S)^{−c'} < ⊤` for `c' < 2`, via
  N2b (`j = 1`, cell hyps discharged) → END 1 → the row-0 shear-peel → the Morse terminal. This is the
  GENERIC-N2b version of what the bespoke `(3,3,4)` route (`step3a`/`ratioResidual`) does by hand for
  `angularR` — the inner half of the weld, the piece that lifts to ∀M.

Codex (xhigh, 2026-06-27, decorrelated) confirmed the design at `r = 2`: the `recStep` entry-chart cover
coincides with the max-modulus `1×1`-minor cover; one N2b level closes the inner `∫_S` UNIFORMLY over the
angular chart (the `Sc → 0` rank-1 edge does not break the comparison — both sides collapse to the Morse
top block), terminating depth-2 without a second radial layer. The certified design has no hole at `r = 2`.

## What this file delivers (S2-FREE, all axiom-clean)

The abstract reduction ends:
* **`schurSplit_integrand_le`** — pointwise inverse-power flip of the N2b two-sided comparison (lower for
  the bound, upper for the zero-guard).
* **`schurSplit_lintegral_le`** — its integral form (core → split-form reduction, given the comparison).
* **`schurSplit_depth2_lt_top`** — the `Fin 4` Morse terminal, finite for `c' < 2` (`= radial_morse…` at
  `m+1 = 4`).

The radial-Morse infra + the inner-S weld:
* **`radial_morse_dominates_absZ_lt_top`** — two-radius Morse dominance over an abstract finite-volume
  `z`-domain (`P`-box radius `Tp`, `z` over any `Z`) — the form the shear-peel feeds.
* **`schurSplitD_eq`** — the N2b `r=2,j=1` split form in explicit scalar shape (top-block shear +
  scaled residual).
* **`schurSplitD_lintegral_lt_top`** — the split-form `S`-integral finite (row-0 shear-peel ⟶ Morse).
* **`schurInner_S_le`** — the inner-S weld CHAINED end-to-end (N2b ⟶ END 1 ⟶ shear-peel ⟶ Morse).

REMAINING (the deferred N4 long pole): the OUTER radial-R blow-up cover — the `recStep`/`g5_pivotNode`
4-chart fold over the `Δ`-box + the radial Jacobian `|a|³` (N1/N3), turning `∫_Δ ∫_S frobSq (Δ·S)^{−c'}`
into the per-chart `∫_a × ∫_{R-ang} ∫_S` that `schurInner_S_le` closes. Mirrors `matBox334_chart_lt_top`.

## S2-hygiene
S2-FREE: the reduction is the elementary inverse-power flip; the Morse terminal is `radial_ball_iff`-based;
the shear-peel is measure-preserving translation. No `monomial_rlct`, no new axiom.
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
the END of the corank-2 N2b→Morse reduction. It takes the split form as its STARTING point — this
ABSTRACT-end lemma does NOT consume `schurSplit_lintegral_le` / `schur_minorPivot_split`. (The genuinely
CHAINED inner-S weld is `schurInner_S_le` below, which DOES invoke N2b and reaches the Morse terminal by a
different route — `schurSplitD_lintegral_lt_top` — not by composing this lemma with `schurSplit_lintegral_le`.)
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

/-! ## Two-radius Morse dominance — the END-2 variant the shear-peel needs

The shear `S_0 ↦ S_0 + R_{01}·S_1` that turns the N2b top block `(R·S)_top` into a free Morse block
enlarges the `P`-box (radius `Tp = 2T` when `|R_{01}·S_1 j| ≤ T`) while the residual parameter `z = S_1`
stays at radius `T`. `radial_morse_dominates_lt_top` uses a single radius; here is its two-radius variant
(the inner `P`-bound `Kbound` is `z`-independent at ANY radius, so the generalisation is immediate). -/

/-- **Two-radius Morse dominance over an abstract `z`-domain.** The `P`-block is a `Fin (m+1)` Morse
block at radius `Tp`; the residual parameter `z` ranges over an arbitrary finite-volume measurable set `Z`
in any measure space (no `Fin k → ℝ` flatten needed). `∫_{z∈Z} ∫_P (∑ⱼ (P j)² + W z)^{−c'} ≤
Kbound (m+1) c' Tp · μ Z < ⊤` for `c' < (m+1)/2`. The `z`-independent inner `P`-bound is `Kbound`;
Tonelli pulls it out. The form the shear-peel feeds (the residual `S`-row over `matBox 1 4 T`). -/
theorem radial_morse_dominates_absZ_lt_top {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (c' : ℝ) (hc' : c' < (m + 1) / 2) (hc0 : 0 ≤ c') (Tp : ℝ) (hTp : 0 < Tp)
    (W : Ω → ℝ) (hWnn : ∀ z, 0 ≤ W z) (Z : Set Ω) (hZ : μ Z < ⊤) :
    ∫⁻ z in Z, (∫⁻ P in morseBox (m + 1) Tp,
        ENNReal.ofReal ((∑ j, (P j) ^ 2 + W z) ^ (-c')) ∂volume) ∂μ < ⊤ := by
  -- inner P-bound: for every z, ∫_P (∑P²+Wz)^{−c'} ≤ Kbound (m+1) c' Tp (z-independent)
  have hinner : ∀ z, ∫⁻ P in morseBox (m + 1) Tp, ENNReal.ofReal ((∑ j, (P j) ^ 2 + W z) ^ (-c'))
      ≤ Kbound (m + 1) c' Tp := by
    intro z
    rw [Kbound]
    -- the Morse-block-zero point is null; off it the pointwise rpow domination (W ≥ 0, −c' ≤ 0)
    have hzero_null : volume {P : Fin (m+1) → ℝ | ∑ j, (P j)^2 = 0} = 0 := by
      have hsub : {P : Fin (m+1) → ℝ | ∑ j, (P j)^2 = 0} ⊆ {(0 : Fin (m+1) → ℝ)} := by
        intro P hP
        simp only [Set.mem_setOf_eq] at hP
        have : ∀ j, (P j)^2 = 0 := fun j =>
          (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).1 hP j (Finset.mem_univ j)
        simp only [Set.mem_singleton_iff]; funext j; exact pow_eq_zero_iff (by norm_num) |>.1 (this j)
      exact measure_mono_null hsub (measure_singleton _)
    refine lintegral_mono_ae ?_
    have hae : ∀ᵐ P : Fin (m+1) → ℝ, ∑ j, (P j)^2 ≠ 0 := by rw [ae_iff]; simpa using hzero_null
    refine (ae_restrict_of_ae hae).mono (fun P hP => ?_)
    apply ENNReal.ofReal_le_ofReal
    have hpos : (0 : ℝ) < ∑ j, (P j)^2 := lt_of_le_of_ne (by positivity) (Ne.symm hP)
    exact Real.rpow_le_rpow_of_nonpos hpos (by linarith [hWnn z]) (by linarith)
  calc ∫⁻ z in Z, (∫⁻ P in morseBox (m + 1) Tp,
          ENNReal.ofReal ((∑ j, (P j) ^ 2 + W z) ^ (-c')) ∂volume) ∂μ
      ≤ ∫⁻ _z in Z, Kbound (m + 1) c' Tp ∂μ := lintegral_mono (fun z => hinner z)
    _ = Kbound (m + 1) c' Tp * μ Z := by rw [setLIntegral_const]
    _ < ⊤ := ENNReal.mul_lt_top (Kbound_lt_top m Tp hTp c' hc') hZ

/-! ## The per-chart inner-S weld — N2b ⟶ shear-peel ⟶ Morse terminal (the genuinely-new weld)

The weld's heart: on a fixed radial-blow-up angular chart (pivot at `(0,0)`, `R 0 0 = 1`, `|R i k| ≤ 1`),
the inner `∫_S frobSq (R·S)^{−c'}` over the `S`-box is finite for `c' < 2`, via N2b (`j = 1`) → END 1
(`schurSplit_lintegral_le`) → the `S`-row split + the row-0 shear-peel (`lintegral_translate_le`,
box-enlarge to radius `3T`) → the two-radius Morse terminal. This CLOSES the inner `∫_S` uniformly over
the chart (Codex-confirmed: one N2b level terminates depth-2; the `Sc → 0` rank-1 edge does not break the
uniform comparison). It is what the existing bespoke `(3,3,4)` route (`step3a`/`ratioResidual`) does by
hand for `angularR`, here via the GENERIC N2b split — the piece that lifts to ∀M.

The radial-blow-up cover producing this chart (the `recStep`/`g5_pivotNode` 4-chart fold over the `Δ`-box
+ the radial Jacobian `|a|³`, mirroring `matBox334_chart_lt_top`) is the remaining mechanical wrapper
(deferred; the bespoke `(3,3,4)` route is the worked reference). -/

/-- The N2b `r = 2, j = 1` split form `D S = frobSq (R·S)_row0 + frobSq (Sc · S_row1)`, abbreviated for
the inner-`S` integral. `(R·S)_row0 : Fin 1 → Fin 4` is the top block; `Sc : Fin 1 → Fin 1` the `1×1`
Schur complement; `S_row1 : Fin 1 → Fin 4` the bottom `S`-row. -/
noncomputable def schurSplitD (R : Fin 2 → Fin 2 → ℝ) (Sc : Matrix (Fin 1) (Fin 1) ℝ)
    (S : Fin 2 → Fin 4 → ℝ) : ℝ :=
  frobSq (fun a : Fin 1 => rmatMul (fun x y => R x y) S ⟨a, by omega⟩)
    + frobSq (rmatMul (fun a b => Sc a b) (fun a : Fin 1 => S ⟨1 + a, by omega⟩))

/-- `schurSplitD ≥ 0` (a sum of two `frobSq`). -/
theorem schurSplitD_nonneg (R : Fin 2 → Fin 2 → ℝ) (Sc : Matrix (Fin 1) (Fin 1) ℝ)
    (S : Fin 2 → Fin 4 → ℝ) : 0 ≤ schurSplitD R Sc S :=
  add_nonneg (frobSq_nonneg _) (frobSq_nonneg _)

/-- **`schurSplitD` in explicit scalar form.** With `R 0 0 = 1`, the top block is the shear
`∑ⱼ (S 0 j + R₀₁·S 1 j)²` and the `1×1` residual is `Sc₀₀²·∑ⱼ (S 1 j)²`:
`schurSplitD R Sc S = (∑ⱼ (S 0 j + R 0 1 · S 1 j)²) + (Sc 0 0)²·(∑ⱼ (S 1 j)²)`. The shear-peel form. -/
theorem schurSplitD_eq (R : Fin 2 → Fin 2 → ℝ) (h00 : R 0 0 = 1) (Sc : Matrix (Fin 1) (Fin 1) ℝ)
    (S : Fin 2 → Fin 4 → ℝ) :
    schurSplitD R Sc S
      = (∑ j, (S 0 j + R 0 1 * S 1 j) ^ 2) + (Sc 0 0) ^ 2 * ∑ j, (S 1 j) ^ 2 := by
  unfold schurSplitD frobSq rmatMul
  congr 1
  · -- top block: ∑_{a:Fin 1} ∑_j (∑_k R_{0k} S_{kj})² = ∑_j (S_{0j} + R₀₁ S_{1j})²
    rw [Fin.sum_univ_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Fin.sum_univ_two]
    have hrow : (⟨((0 : Fin 1) : ℕ), by omega⟩ : Fin 2) = (0 : Fin 2) := by ext; simp
    rw [hrow, h00]; ring
  · -- residual: ∑_{a:Fin 1} ∑_j (∑_{b:Fin 1} Sc_{ab} S_{1+b,j})² = Sc₀₀² ∑_j S_{1j}²
    rw [Fin.sum_univ_one, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Fin.sum_univ_one]
    have hb : S (⟨1 + ((0 : Fin 1) : ℕ), by omega⟩ : Fin 2) j = S (1 : Fin 2) j := by
      congr 1
    rw [hb]; ring

/-- **Translation box-enlarge bound** (local copy of the `RouteM334Ratiofin` atom, avoiding the heavy
import): `∫_{v∈B} f(v + s) ≤ ∫_{w∈BG} f w` when `(·+s) '' B ⊆ BG`. Measure-preserving translation
(`measurePreserving_add_right`) + `lintegral_mono_set`. -/
theorem lintegral_translate_le_local (n : ℕ) (s : Fin n → ℝ)
    (B BG : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ≥0∞)
    (hsub : (fun v => v + s) '' B ⊆ BG) :
    (∫⁻ v in B, f (v + s)) ≤ ∫⁻ w in BG, f w := by
  set τ : (Fin n → ℝ) → (Fin n → ℝ) := fun v => v + s with hτ
  have hmp : MeasurePreserving τ volume volume := measurePreserving_add_right volume s
  have hemb : MeasurableEmbedding τ := (Homeomorph.addRight s).measurableEmbedding
  have h1 : (∫⁻ v in B, f (τ v)) = ∫⁻ w in τ '' B, f w := by
    rw [← hmp.setLIntegral_comp_preimage_emb hemb f (τ '' B), Set.preimage_image_eq B hemb.injective]
  calc (∫⁻ v in B, f (v + s)) = ∫⁻ w in τ '' B, f w := h1
    _ ≤ ∫⁻ w in BG, f w := lintegral_mono_set hsub

/-- `matBox p n T` is a product of compact intervals, hence finite volume. -/
theorem matBox_volume_lt_top (p n : ℕ) (T : ℝ) : volume (matBox p n T) < ⊤ := by
  have heq : matBox p n T
      = Set.univ.pi (fun _ : Fin p => Set.univ.pi (fun _ : Fin n => Set.Icc (-T) T)) := by
    ext X; simp only [matBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  rw [heq]
  exact (isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))).measure_lt_top

/-- **The split-form `S`-integral finiteness (the shear-peel ⟶ Morse terminal, PROVED, S2-FREE).**
`∫_{S ∈ matBox 2 4 T} (schurSplitD R Sc S)^{−c'} < ⊤` for `0 < c' < 2`. By `schurSplitD_eq` the integrand
is `(∑ⱼ (S 0 j + R₀₁·S 1 j)² + Sc₀₀²·∑ⱼ (S 1 j)²)^{−c'}`; row-split `S = (S_row0, S_row1)`
(`piFinSuccAbove 0`, MP) + Tonelli (`S_row1` outermost); per fixed `S_row1` the top block is a shear of
`S_row0` (peeled by `lintegral_translate_le_local`, box-enlarge to radius `2T` since `|R₀₁·S_row1 j| ≤ T`),
the residual `Sc₀₀²·∑ⱼ (S_row1 j)² ≥ 0` depends only on `S_row1`; the abstract-`Z` Morse terminal
(`radial_morse_dominates_absZ_lt_top`, `m+1 = 4`, `Tp = 2T`, `Z = matBox 1 4 T`) closes it for `c' < 2`. -/
theorem schurSplitD_lintegral_lt_top (R : Fin 2 → Fin 2 → ℝ) (Sc : Matrix (Fin 1) (Fin 1) ℝ)
    (h00 : R 0 0 = 1) (hbd : ∀ i k, |R i k| ≤ 1) (c' : ℝ) (hc0 : 0 < c') (hc' : c' < 2)
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ S in matBox 2 4 T, ENNReal.ofReal ((schurSplitD R Sc S) ^ (-c')) < ⊤ := by
  -- the integrand in explicit scalar form (top-block shear + scaled residual)
  have hint : ∀ S : Fin 2 → Fin 4 → ℝ,
      ENNReal.ofReal ((schurSplitD R Sc S) ^ (-c'))
        = ENNReal.ofReal (((∑ j, (S 0 j + R 0 1 * S 1 j) ^ 2)
            + (Sc 0 0) ^ 2 * ∑ j, (S 1 j) ^ 2) ^ (-c')) := by
    intro S; rw [schurSplitD_eq R h00 Sc S]
  rw [setLIntegral_congr_fun (matBox_measurableSet 2 4 T) (fun S _ => hint S)]
  -- row-split S = (row0, S1) via piFinSuccAbove 0 on the ROW index
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 2 => Fin 4 → ℝ) 0 with he
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin 2 => Fin 4 → ℝ) 0
  -- the joint integrand as a function of q = (row0, S1)
  set H : (Fin 4 → ℝ) × (Fin 1 → Fin 4 → ℝ) → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (((∑ j, (q.1 j + R 0 1 * q.2 0 j) ^ 2)
      + (Sc 0 0) ^ 2 * ∑ j, (q.2 0 j) ^ 2) ^ (-c')) with hHdef
  have hHmeas : Measurable H := by
    rw [hHdef]
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    refine Measurable.add ?_ ?_
    · refine Finset.measurable_sum _ (fun j _ => (Measurable.pow_const ?_ 2))
      have h0 : Measurable (fun q : (Fin 4 → ℝ) × (Fin 1 → Fin 4 → ℝ) => q.1 j) :=
        (measurable_pi_apply j).comp measurable_fst
      have h2 : Measurable (fun q : (Fin 4 → ℝ) × (Fin 1 → Fin 4 → ℝ) => q.2 0 j) :=
        (measurable_pi_apply j).comp ((measurable_pi_apply 0).comp measurable_snd)
      exact h0.add (measurable_const.mul h2)
    · refine measurable_const.mul (Finset.measurable_sum _ (fun j _ => (Measurable.pow_const ?_ 2)))
      exact (measurable_pi_apply j).comp ((measurable_pi_apply 0).comp measurable_snd)
  -- matBox 2 4 T = e ⁻¹' (morseBox 4 T ×ˢ matBox 1 4 T)
  have hsplit : matBox 2 4 T = e ⁻¹' (morseBox 4 T ×ˢ matBox 1 4 T) := by
    ext S
    simp only [he, Set.mem_preimage, Set.mem_prod, matBox, morseBox, Set.mem_setOf_eq, Set.mem_pi,
      Set.mem_univ, true_implies]
    constructor
    · intro h; exact ⟨fun j => h 0 j, fun i k => h i.succ k⟩
    · rintro ⟨h1, h2⟩ i k
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
      · exact h1 k
      · exact h2 i' k
  -- transport the integral to the product domain
  have hLHS : (∫⁻ S in matBox 2 4 T,
      ENNReal.ofReal (((∑ j, (S 0 j + R 0 1 * S 1 j) ^ 2)
        + (Sc 0 0) ^ 2 * ∑ j, (S 1 j) ^ 2) ^ (-c')))
      = ∫⁻ q in (morseBox 4 T ×ˢ matBox 1 4 T), H q := by
    rw [hsplit, ← hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding H
        (morseBox 4 T ×ˢ matBox 1 4 T)]
    refine setLIntegral_congr_fun ?_ (fun S _ => rfl)
    exact e.measurable (MeasurableSet.prod (morseBox_measurableSet 4 T) (matBox_measurableSet 1 4 T))
  rw [hLHS]
  -- Tonelli reorder: S1 outermost, row0 inner
  rw [Measure.volume_eq_prod, setLIntegral_prod _ hHmeas.aemeasurable, lintegral_lintegral_swap
    hHmeas.aemeasurable]
  -- per fixed S1: translate row0 ↦ row0 + shift (shift_j = R₀₁·S1₀ⱼ, |·| ≤ T), box-enlarge to 2T,
  -- then ≤ ∫_{P∈morseBox 4 (2T)} (∑(P j)² + W S1)^{−c'} with W S1 = Sc₀₀²·∑(S1₀ⱼ)²
  refine lt_of_le_of_lt
    (setLIntegral_mono_ae' (matBox_measurableSet 1 4 T) (ae_of_all _ (fun S1 hS1 => ?_)))
    (radial_morse_dominates_absZ_lt_top (m := 3) volume c' (by norm_num; linarith) (le_of_lt hc0)
      (2 * T) (by linarith) (fun S1 : Fin 1 → Fin 4 → ℝ => (Sc 0 0) ^ 2 * ∑ j, (S1 0 j) ^ 2)
      (fun S1 => by positivity) (matBox 1 4 T) (matBox_volume_lt_top 1 4 T))
  -- the per-S1 row0-translate bound
  set shift : Fin 4 → ℝ := fun j => R 0 1 * S1 0 j with hshift
  set f : (Fin 4 → ℝ) → ℝ≥0∞ := fun P =>
    ENNReal.ofReal (((∑ j, (P j) ^ 2) + (Sc 0 0) ^ 2 * ∑ j, (S1 0 j) ^ 2) ^ (-c')) with hf
  have hrw : ∀ row0 : Fin 4 → ℝ, H (row0, S1) = f (row0 + shift) := by
    intro row0; rw [hHdef, hf]; rfl
  rw [lintegral_congr hrw]
  refine lintegral_translate_le_local 4 shift (morseBox 4 T) (morseBox 4 (2 * T)) f ?_
  -- the box-enlarge: |row0 j + shift j| ≤ T + T = 2T
  rintro P ⟨v, hv, rfl⟩
  simp only [morseBox, Set.mem_pi, Set.mem_univ, true_implies] at hv ⊢
  intro j
  have hvj := Set.mem_Icc.1 (hv j)
  have hS1j := Set.mem_Icc.1 (hS1 0 j)
  have hR01 := abs_le.1 (hbd 0 1)
  have hshiftbd : -T ≤ R 0 1 * S1 0 j ∧ R 0 1 * S1 0 j ≤ T := by
    constructor <;>
      nlinarith [hR01.1, hR01.2, hS1j.1, hS1j.2, sq_nonneg (R 0 1 + S1 0 j),
        sq_nonneg (R 0 1 - S1 0 j), hT.le]
  rw [Set.mem_Icc, Pi.add_apply, hshift]
  constructor <;> [nlinarith [hvj.1, hshiftbd.1]; nlinarith [hvj.2, hshiftbd.2]]

/-- **The per-chart inner-S finiteness (the weld heart, S2-FREE).** On a radial-blow-up angular chart
(`R 0 0 = 1`, `|R i k| ≤ 1` — the bounded pivot-`(0,0)` cell), `∫_{S ∈ matBox 2 4 T} frobSq (R·S)^{−c'}`
is finite for `0 < c' < 2 = λ_{2,4}`. Via N2b (`j = 1`, cell hyps discharged from `R 0 0 = 1` being a
max-modulus entry) → `schurSplit_lintegral_le` (END 1, the corank-2 → split-form reduction) → the
split-form `S`-integral, which the next lemma closes by the row-0 shear-peel + the two-radius Morse
terminal. SKELETON pending the split-form `S`-integral (`schurSplitD_lintegral_lt_top`). -/
theorem schurInner_S_le (R : Fin 2 → Fin 2 → ℝ) (h00 : R 0 0 = 1) (hbd : ∀ i k, |R i k| ≤ 1)
    (c' : ℝ) (hc0 : 0 < c') (hc' : c' < 2) (T : ℝ) (hT : 0 < T) :
    ∫⁻ S in matBox 2 4 T, ENNReal.ofReal ((frobSq (rmatMul (fun a b => R a b) S)) ^ (-c')) < ⊤ := by
  -- N2b at r = 2, j = 1: the uniform two-sided comparison on the bounded pivot-(0,0) cell.
  obtain ⟨c₀, c₁, hc₀, hc₁, hN2b⟩ := schur_minorPivot_split (r := 2) (p := 4) 1 (by norm_num)
  -- the cell hypotheses: |R a b| ≤ 1 (given), the 1×1 minor R₀₀ = 1 is max-modulus, det ≠ 0
  have hbdM : ∀ a b : Fin 2, |(Matrix.of (fun a b => R a b)) a b| ≤ 1 := hbd
  -- the 1×1 top-left minor det = R 0 0 = 1
  have hpivdet : (Matrix.of (fun a b : Fin 1 =>
      (Matrix.of (fun a b => R a b)) ⟨a, by omega⟩ ⟨b, by omega⟩)).det = 1 := by
    rw [Matrix.det_fin_one]; simpa using h00
  have hpivot : ∀ (I J : Fin 1 → Fin 2),
      |((Matrix.of (fun a b => R a b)).submatrix I J).det|
        ≤ |(Matrix.of (fun a b : Fin 1 =>
            (Matrix.of (fun a b => R a b)) ⟨a, by omega⟩ ⟨b, by omega⟩)).det| := by
    intro I J
    rw [Matrix.det_fin_one, hpivdet, abs_one, Matrix.submatrix_apply, Matrix.of_apply]
    exact hbd (I 0) (J 0)
  have hne : (Matrix.of (fun a b : Fin 1 =>
      (Matrix.of (fun a b => R a b)) ⟨a, by omega⟩ ⟨b, by omega⟩)).det ≠ 0 := by
    rw [hpivdet]; norm_num
  -- N2b applied at the FIXED R, per S: the split form `D S` (Sc is R-determined, the same for all S).
  -- Extract the Schur complement once (it depends only on R); the bounds hold ∀ S with that Sc.
  set RM : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of (fun a b => R a b) with hRM
  obtain ⟨Sc, hSceq, _hdet, _, _⟩ := hN2b RM (fun _ _ => 0) hbdM hpivot hne
  -- per-S bounds, with the SAME Sc (uniqueness: N2b's Sc equals the R-formula `hSceq`)
  have hbounds : ∀ S : Fin 2 → Fin 4 → ℝ,
      c₀ * schurSplitD R Sc S ≤ frobSq (rmatMul (fun a b => R a b) S)
        ∧ frobSq (rmatMul (fun a b => R a b) S) ≤ c₁ * schurSplitD R Sc S := by
    intro S
    obtain ⟨Sc', hSceq', _, hlo, hup⟩ := hN2b RM S hbdM hpivot hne
    have hSceq2 : Sc' = Sc := by rw [hSceq', ← hSceq]
    subst hSceq2
    exact ⟨hlo, hup⟩
  -- END 1 (`schurSplit_lintegral_le`): reduce the core integral to the split-form integral.
  refine lt_of_le_of_lt (schurSplit_lintegral_le volume c₀ c₁ hc₀
    (fun S => schurSplitD R Sc S) (fun S => frobSq (rmatMul (fun a b => R a b) S))
    (matBox 2 4 T) (fun S => schurSplitD_nonneg R Sc S) (fun S => frobSq_nonneg _)
    (fun S => (hbounds S).1) (fun S => (hbounds S).2) c' hc0) ?_
  -- the split-form S-integral is finite (shear-peel + two-radius Morse terminal)
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (schurSplitD_lintegral_lt_top R Sc h00 hbd c' hc0 hc' T hT)

end DLNFibre.DLN.RLCT
