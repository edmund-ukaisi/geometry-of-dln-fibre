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
split-form `S`-integral, closed by the row-0 shear-peel + the Morse terminal
(`schurSplitD_lintegral_lt_top`). PROVED sorry-free. (The uniform-`≤` form is `schurInner_S_bound`, which
the outer cover `matBox2_chart_lt_top` consumes; this `< ⊤` form is the standalone inner-S statement.) -/
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

/-! ## The OUTER radial-Δ blow-up cover — the joint corank-2 core finiteness via the Schur route

The outer half of the depth-2 weld: cover the `2×2` `Δ`-box by the `r² = 4` max-modulus-entry charts
(`recStep`/`g5_pivotNode` on the `Fin 4` flat carrier), pull the radial scale `a` out of each chart
(Jacobian `|a|³` via `pivotBlowupOnDeriv_det`, the N1 degree-2 homogeneity), Tonelli-separate the a-axis
divisor (N3a, `c' < r²/2 = 2`) from the inner angular `∫_{R-ang}∫_S`, and close the inner integral by
`schurInner_S_le` (the inner-S weld). This CHAINS the two halves into the joint corank-2 core finiteness
`∫_Δ ∫_S frobSq (Δ·S)^{−c'} < ⊤` for `c' < 2 = λ_{2,4}` — the depth-2 weld END-TO-END (the Schur-route
re-proof of `core334_lt_top`'s `(3,3,4)` corank-2 core, validating the generic recursion path).

Mirrors `matBox334_chart_lt_top`'s radial-CoV plumbing at scale `r² = 4` (the `(3,3,4)` route does this
for its 9 A0-entry charts). The small flatten/box atoms are copied locally (avoiding the heavy
`RouteM334Hfin` import). -/

/-- Local `matToFlatEquiv 2 2 : (Fin 2 → Fin 2 → ℝ) ≃ᵐ (Fin 4 → ℝ)` (avoiding the heavy `RouteM334Hfin`
import): uncurry + the `Fin 2 × Fin 2 ≃ Fin 4` index reindex. -/
noncomputable def matToFlat2 : (Fin 2 → Fin 2 → ℝ) ≃ᵐ (Fin (2 * 2) → ℝ) :=
  (MeasurableEquiv.piCurry (fun (_ : Fin 2) (_ : Fin 2) => ℝ)).symm.trans
    (MeasurableEquiv.arrowCongr'
      ((Equiv.sigmaEquivProd (Fin 2) (Fin 2)).trans finProdFinEquiv) (MeasurableEquiv.refl ℝ))

theorem measurePreserving_matToFlat2 :
    MeasurePreserving matToFlat2 (volume : Measure (Fin 2 → Fin 2 → ℝ))
      (volume : Measure (Fin (2 * 2) → ℝ)) := by
  unfold matToFlat2
  refine MeasurePreserving.trans ?_ (volume_preserving_arrowCongr'
    ((Equiv.sigmaEquivProd (Fin 2) (Fin 2)).trans finProdFinEquiv)
    (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _))
  exact (measurePreserving_piCurry (fun (_ : Fin 2) (_ : Fin 2) => ℝ)
    (fun _ _ => (volume : Measure ℝ))).symm
    (MeasurableEquiv.piCurry (fun (_ : Fin 2) (_ : Fin 2) => ℝ))

/-- The flattened `Δ`-box on the `Fin 4` carrier: `[−T,T]^4`. -/
def flatBox2 (T : ℝ) : Set (Fin (2 * 2) → ℝ) := {y | ∀ i, y i ∈ Set.Icc (-T) T}

theorem flatBox2_measurableSet (T : ℝ) : MeasurableSet (flatBox2 T) := by
  rw [flatBox2, Set.setOf_forall]
  exact MeasurableSet.iInter (fun i => (measurable_pi_apply i) measurableSet_Icc)

/-- `matBox 2 2 T = matToFlat2 ⁻¹' flatBox2 T` (coordinatewise; the entry↔`Fin 4` reindex). -/
theorem matBox2_flatBox_preimage (T : ℝ) : matBox 2 2 T = matToFlat2 ⁻¹' flatBox2 T := by
  ext Δ
  simp only [matBox, flatBox2, Set.mem_setOf_eq, Set.mem_preimage]
  set e : (Σ _ : Fin 2, Fin 2) ≃ Fin (2 * 2) :=
    (Equiv.sigmaEquivProd (Fin 2) (Fin 2)).trans finProdFinEquiv with he
  have hcoord : ∀ i : Fin (2 * 2), (matToFlat2 Δ) i = Δ (e.symm i).1 (e.symm i).2 := fun i => rfl
  constructor
  · intro h i; rw [hcoord i]; exact h (e.symm i).1 (e.symm i).2
  · intro h k j
    have := h (e ⟨k, j⟩)
    rw [hcoord (e ⟨k, j⟩), Equiv.symm_apply_apply] at this
    exact this

/-- The flat-`Δ` cover integrand: `gFlat2 c' T y = ∫_{S∈box} frobSq(rmatMul (matToFlat2.symm y) S)^{−c'}`,
the (`S`-integrated) `Δ`-integrand reindexed by the `Fin 4` flatten. The `g` of `recStep` on `Fin 4`. -/
noncomputable def gFlat2 (c' : ℝ) (T : ℝ) (y : Fin (2 * 2) → ℝ) : ℝ≥0∞ :=
  ∫⁻ S in matBox 2 4 T,
    ENNReal.ofReal ((frobSq (rmatMul (matToFlat2.symm y) S)) ^ (-c'))

/-- The `Δ`-outer integral reindexes to the flat `gFlat2` integral over `flatBox2`
(via `measurePreserving_matToFlat2` + `matBox2_flatBox_preimage`). -/
theorem matBox2_outer_flat (c' : ℝ) (T : ℝ) :
    (∫⁻ Δ in matBox 2 2 T, ∫⁻ S in matBox 2 4 T,
        ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c')))
      = ∫⁻ y in flatBox2 T, gFlat2 c' T y := by
  have hmp := measurePreserving_matToFlat2
  have hcomp := hmp.setLIntegral_comp_preimage_emb matToFlat2.measurableEmbedding
    (gFlat2 c' T) (flatBox2 T)
  rw [matBox2_flatBox_preimage, ← hcomp]
  refine setLIntegral_congr_fun (matToFlat2.measurable (flatBox2_measurableSet T)) (fun Δ _ => ?_)
  rw [gFlat2, MeasurableEquiv.symm_apply_apply]

/-- The cover-to-sum on the `Fin 4` flat carrier: `∫_{flatBox2} gFlat2 = ∑_{p} ∫_{chart p} |det|·
gFlat2(blowup)`, via `recStep` (the `univ` argmax-cover of the 4 `Δ`-entries). -/
theorem gFlat2_cover_sum (c' : ℝ) (T : ℝ) :
    (∫⁻ y in flatBox2 T, gFlat2 c' T y)
      = ∑ p ∈ (Finset.univ : Finset (Fin (2 * 2))),
          ∫⁻ y in chartDomOn (Finset.univ : Finset (Fin (2 * 2))) p \ pivotZeroOn p,
            ENNReal.ofReal |(pivotBlowupOnDeriv (Finset.univ : Finset (Fin (2 * 2))) p y).det|
              * (flatBox2 T).indicator (gFlat2 c' T) (pivotBlowupOn
                  (Finset.univ : Finset (Fin (2 * 2))) p y) := by
  exact recStep (Finset.univ : Finset (Fin (2 * 2))) 0 (Finset.mem_univ 0)
    (flatBox2 T) (flatBox2_measurableSet T) (gFlat2 c' T)

/-- The unflattened angular matrix on chart `p`: `Rmat2 p y` is the `2×2` matrix with `R_p = 1` and
`R_k = y_k` (`k ≠ p`) — the bounded direction of the radial blow-up `Δ = (y p)·R`. -/
noncomputable def Rmat2 (p : Fin (2 * 2)) (y : Fin (2 * 2) → ℝ) : Fin 2 → Fin 2 → ℝ :=
  matToFlat2.symm (fun i => if i = p then 1 else y i)

/-- **The radial pull-out (the homogeneity step).** `gFlat2 c' T` of the pivot blow-up factors the radial
scale `a = y p` out with degree `2` (`radialDelta_loss_factor`): the blown-up flat `Δ` unflattens to
`(y p) • (Rmat2 p y)`, so `gFlat2 c' T (blowup) = ∫_S ofReal(((y p)²·frobSq(Rmat2·S))^{−c'})`. -/
theorem gFlat2_blowup_radial (c' : ℝ) (T : ℝ) (p : Fin (2 * 2)) (y : Fin (2 * 2) → ℝ) :
    gFlat2 c' T (pivotBlowupOn (Finset.univ : Finset (Fin (2 * 2))) p y)
      = ∫⁻ S in matBox 2 4 T,
          ENNReal.ofReal (((y p) ^ 2 * frobSq (rmatMul (Rmat2 p y) S)) ^ (-c')) := by
  unfold gFlat2 Rmat2
  refine lintegral_congr (fun S => ?_)
  congr 1
  have hbl : matToFlat2.symm (pivotBlowupOn (Finset.univ : Finset (Fin (2 * 2))) p y)
      = fun r c => (y p) * (matToFlat2.symm (fun i => if i = p then 1 else y i)) r c := by
    funext r c
    show matToFlat2.symm (pivotBlowupOn (Finset.univ : Finset (Fin (2 * 2))) p y) r c = _
    rw [show pivotBlowupOn (Finset.univ : Finset (Fin (2 * 2))) p y
        = (fun i => (y p) * (if i = p then 1 else y i)) from by
      funext i; unfold pivotBlowupOn
      by_cases hi : i = p
      · subst hi; simp
      · simp [hi]]
    -- matToFlat2.symm is linear in the flat vector entrywise (a reindex), so the scalar pulls through
    show matToFlat2.symm (fun i => (y p) * (if i = p then 1 else y i)) r c
        = (y p) * matToFlat2.symm (fun i => if i = p then 1 else y i) r c
    rfl
  rw [hbl, radialDelta_loss_factor (y p) (matToFlat2.symm (fun i => if i = p then 1 else y i)) S]

/-! ### Perm-invariance atoms (bring an arbitrary pivot to `(0,0)`) -/

/-- `frobSq (R·S)` is invariant under a row-perm `σr` of `R` + a simultaneous col-perm `σc` of `R`
(= row-perm of `S`). The 2×2 / `Fin 4` analog of `frobSq_rmatMul_perm`. -/
theorem frobSq_rmatMul_perm2 (R : Fin 2 → Fin 2 → ℝ) (S : Fin 2 → Fin 4 → ℝ) (σr σc : Fin 2 ≃ Fin 2) :
    frobSq (rmatMul R S)
      = frobSq (rmatMul (fun r c => R (σr r) (σc c)) (fun k j => S (σc k) j)) := by
  unfold frobSq rmatMul
  rw [← Equiv.sum_comp σr (fun r => ∑ j, (∑ k, R r k * S k j) ^ 2)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  congr 1
  rw [← Equiv.sum_comp σc (fun k => R (σr r) k * S k j)]

/-- The `S` row-permutation change of variables on the symmetric box `matBox 2 4 T`: permuting the
`Fin 2` row-index of `S` by `σc` is measure-preserving (`piCongrLeft`) and the box is `σc`-invariant. -/
theorem matBox24_rowperm_lintegral (T : ℝ) (σc : Fin 2 ≃ Fin 2) (f : (Fin 2 → Fin 4 → ℝ) → ℝ≥0∞) :
    (∫⁻ S in matBox 2 4 T, f S) = ∫⁻ S in matBox 2 4 T, f (fun k j => S (σc k) j) := by
  set E := MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => Fin 4 → ℝ) σc with hE
  have hmp : MeasurePreserving E.symm volume volume :=
    (volume_measurePreserving_piCongrLeft (fun _ : Fin 2 => Fin 4 → ℝ) σc).symm E
  have hpre : matBox 2 4 T = E.symm ⁻¹' (matBox 2 4 T) := by
    ext S
    simp only [Set.mem_preimage, matBox, Set.mem_setOf_eq]
    constructor
    · intro h i k; exact h (σc i) k
    · intro h i k
      have := h (σc.symm i) k
      rw [show E.symm S (σc.symm i) k = S i k from by
        show S (σc (σc.symm i)) k = S i k; rw [Equiv.apply_symm_apply]] at this
      exact this
  have key := hmp.setLIntegral_comp_preimage_emb E.symm.measurableEmbedding f (matBox 2 4 T)
  have hrhs : (∫⁻ S in matBox 2 4 T, f (fun k j => S (σc k) j))
      = ∫⁻ S in matBox 2 4 T, f (E.symm S) := rfl
  rw [hrhs]
  rw [← hpre] at key
  exact key.symm

/-- **Inner-S finiteness at an ARBITRARY pivot** (the per-chart plug). For `R` with `R i₀ j₀ = 1`
(any entry) and `|R i k| ≤ 1`, `∫_{S∈matBox 2 4 T} frobSq (R·S)^{−c'} < ⊤` for `0 < c' < 2`: swap the
pivot row/col to `(0,0)` (`Equiv.swap`, `frobSq_rmatMul_perm2` + `matBox24_rowperm_lintegral` MP) and
apply `schurInner_S_le`. The pivot-(0,0) chart is the `σ = id` special case. -/
theorem schurInner_S_le_pivot (R : Fin 2 → Fin 2 → ℝ) (i₀ j₀ : Fin 2) (hpiv : R i₀ j₀ = 1)
    (hbd : ∀ i k, |R i k| ≤ 1) (c' : ℝ) (hc0 : 0 < c') (hc' : c' < 2) (T : ℝ) (hT : 0 < T) :
    ∫⁻ S in matBox 2 4 T, ENNReal.ofReal ((frobSq (rmatMul (fun a b => R a b) S)) ^ (-c')) < ⊤ := by
  set σr := Equiv.swap i₀ 0 with hσr
  set σc := Equiv.swap j₀ 0 with hσc
  -- permuted matrix R' r c = R (σr r) (σc c); R' 0 0 = R i₀ j₀ = 1, |R' i k| ≤ 1
  set R' : Fin 2 → Fin 2 → ℝ := fun r c => R (σr r) (σc c) with hR'
  have h00' : R' 0 0 = 1 := by
    show R (σr 0) (σc 0) = 1
    rw [hσr, hσc, Equiv.swap_apply_right, Equiv.swap_apply_right]; exact hpiv
  have hbd' : ∀ i k, |R' i k| ≤ 1 := fun i k => hbd (σr i) (σc k)
  -- rewrite the integrand by frobSq perm-invariance, then row-perm the S-box (MP)
  have hrw : ∀ S : Fin 2 → Fin 4 → ℝ,
      ENNReal.ofReal ((frobSq (rmatMul (fun a b => R a b) S)) ^ (-c'))
        = ENNReal.ofReal ((frobSq (rmatMul (fun a b => R' a b) (fun k j => S (σc k) j))) ^ (-c')) := by
    intro S; rw [frobSq_rmatMul_perm2 R S σr σc]
  rw [setLIntegral_congr_fun (matBox_measurableSet 2 4 T) (fun S _ => hrw S)]
  rw [← matBox24_rowperm_lintegral T σc
    (fun S => ENNReal.ofReal ((frobSq (rmatMul (fun a b => R' a b) S)) ^ (-c')))]
  exact schurInner_S_le R' h00' hbd' c' hc0 hc' T hT

/-! ### The per-chart finiteness + the assembly -/

/-- The matrix↔flat index equiv `e2 : Fin 2 × Fin 2 ≃ Fin 4`, `e2 (i,j) = matToFlat2-index`. -/
noncomputable def e2 : Fin 2 × Fin 2 ≃ Fin (2 * 2) :=
  ((Equiv.sigmaEquivProd (Fin 2) (Fin 2)).symm).trans
    ((Equiv.sigmaEquivProd (Fin 2) (Fin 2)).trans finProdFinEquiv)

/-- `Rmat2 p y i j = if e2 (i,j) = p then 1 else y (e2 (i,j))` — the unflattened "1 at the pivot, `y`
elsewhere" angular matrix entrywise. -/
theorem Rmat2_entry (p : Fin (2 * 2)) (y : Fin (2 * 2) → ℝ) (i j : Fin 2) :
    Rmat2 p y i j = if e2 (i, j) = p then 1 else y (e2 (i, j)) := rfl

/-- The pivot entry of `Rmat2 p y` is `1` (at the matrix index `e2.symm p`). -/
theorem Rmat2_pivot (p : Fin (2 * 2)) (y : Fin (2 * 2) → ℝ) :
    Rmat2 p y (e2.symm p).1 (e2.symm p).2 = 1 := by
  rw [Rmat2_entry]
  rw [if_pos]
  rw [show ((e2.symm p).1, (e2.symm p).2) = e2.symm p from rfl, Equiv.apply_symm_apply]

/-- Off-pivot entries of `Rmat2 p y` are `y`-components, hence `|·| ≤ 1` on the ratio chart `|y_k| ≤ 1`
(`k ≠ p`); the pivot entry is `1`. So `|Rmat2 p y i j| ≤ 1` everywhere on the chart. -/
theorem Rmat2_entry_le (p : Fin (2 * 2)) (y : Fin (2 * 2) → ℝ)
    (hy : ∀ k, k ≠ p → |y k| ≤ 1) (i j : Fin 2) : |Rmat2 p y i j| ≤ 1 := by
  rw [Rmat2_entry]
  by_cases h : e2 (i, j) = p
  · rw [if_pos h]; norm_num
  · rw [if_neg h]; exact hy _ h

/-- The inner angular S-integral on chart `p` (the ratio-residual): `innerS2 c' T p y = ∫_{S∈box}
frobSq(Rmat2 p y · S)^{−c'}`. Reads `y` only through the off-pivot ratios (`Rmat2 p y` ignores `y p`). -/
noncomputable def innerS2 (c' : ℝ) (T : ℝ) (p : Fin (2 * 2)) (y : Fin (2 * 2) → ℝ) : ℝ≥0∞ :=
  ∫⁻ S in matBox 2 4 T, ENNReal.ofReal ((frobSq (rmatMul (Rmat2 p y) S)) ^ (-c'))

/-- `innerS2` is `y p`-invariant: `Rmat2 p y` reads `y i` only for `i ≠ p` (the pivot entry is `1`). -/
theorem innerS2_offpivot (c' : ℝ) (T : ℝ) (p : Fin (2 * 2)) (y y' : Fin (2 * 2) → ℝ)
    (h : ∀ i, i ≠ p → y i = y' i) : innerS2 c' T p y = innerS2 c' T p y' := by
  have hR : Rmat2 p y = Rmat2 p y' := by
    funext i j; rw [Rmat2_entry, Rmat2_entry]
    by_cases hij : e2 (i, j) = p
    · rw [if_pos hij, if_pos hij]
    · rw [if_neg hij, if_neg hij]; exact h _ hij
  rw [innerS2, innerS2, hR]

/-- `innerS2 c' T p` is measurable in `y` (the S-integral of the measurable joint integrand). -/
theorem measurable_innerS2 (c' : ℝ) (T : ℝ) (p : Fin (2 * 2)) : Measurable (innerS2 c' T p) := by
  unfold innerS2
  apply Measurable.lintegral_prod_right (f := fun y S =>
    ENNReal.ofReal ((frobSq (rmatMul (Rmat2 p y) S)) ^ (-c')))
  apply ENNReal.measurable_ofReal.comp
  apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
  unfold frobSq rmatMul
  apply Finset.measurable_sum; intro i _
  apply Finset.measurable_sum; intro j _
  apply Measurable.pow_const
  apply Finset.measurable_sum; intro k _
  apply Measurable.mul
  · -- Rmat2 p y i k is measurable in y (it is `if … then 1 else y (e2 (i,k))`)
    have hy : Measurable (fun y : Fin (2 * 2) → ℝ => Rmat2 p y i k) := by
      simp only [Rmat2_entry]
      by_cases h : e2 (i, k) = p
      · simp only [if_pos h]; exact measurable_const
      · simp only [if_neg h]; exact measurable_pi_apply _
    exact hy.comp measurable_fst
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply k).comp measurable_snd)

/-- On `chartDomOn univ p` (ratios `|y_k| ≤ T·…`, here the radial chart uses radius `1` for the ratios),
the blown-up point lands in `flatBox2 T` IFF the radial coordinate `|y p| ≤ T`. The box indicator depends
only on `|y p|` — decoupling the radial axis from the 3 ratios. (Chart ratios at radius `1`, the box at
radius `T`: off-pivot blown-up entries are `y p · y_k`, `|y_k| ≤ 1`, so `|y p · y_k| ≤ |y p|`.) -/
theorem flatBox2_blowup_mem_iff (T : ℝ) (p : Fin (2 * 2)) (y : Fin (2 * 2) → ℝ)
    (hy : y ∈ chartDomOn (Finset.univ : Finset (Fin (2 * 2))) p) :
    pivotBlowupOn (Finset.univ : Finset (Fin (2 * 2))) p y ∈ flatBox2 T ↔ |y p| ≤ T := by
  unfold flatBox2 chartDomOn at *
  simp only [Set.mem_setOf_eq] at *
  constructor
  · intro h
    have hpp := h p
    rw [pivotBlowupOn] at hpp
    simp only [if_pos rfl, Set.mem_Icc] at hpp
    rw [abs_le]; exact hpp
  · intro hp i
    rw [pivotBlowupOn]
    by_cases hi : i = p
    · subst hi; simp only [if_pos rfl, Set.mem_Icc]; rw [abs_le] at hp; exact hp
    · simp only [if_neg hi, Finset.mem_univ, if_true, Set.mem_Icc]
      have hyi : |y i| ≤ 1 := hy i (Finset.mem_univ i) hi
      have hb : |y p * y i| ≤ |y p| := by
        rw [abs_mul]; nlinarith [abs_nonneg (y p), abs_nonneg (y i), abs_nonneg (y p * y i)]
      have hbb : |y p * y i| ≤ T := le_trans hb hp
      rw [abs_le] at hbb; exact hbb

/-! ### Uniform bounds — the ratio-residual integral needs a `y`-independent bound, not just `< ⊤` -/

/-- The `≤`-form of the abstract-`Z` Morse terminal: `∫_z ∫_P (∑(P j)² + W z)^{−c'} ≤ Kbound (m+1) c' Tp ·
μ Z` (the explicit `R`-independent bound the `< ⊤` form proves internally). -/
theorem radial_morse_dominates_absZ_le {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (c' : ℝ) (hc' : c' < (m + 1) / 2) (hc0 : 0 ≤ c') (Tp : ℝ) (hTp : 0 < Tp)
    (W : Ω → ℝ) (hWnn : ∀ z, 0 ≤ W z) (Z : Set Ω) :
    ∫⁻ z in Z, (∫⁻ P in morseBox (m + 1) Tp,
        ENNReal.ofReal ((∑ j, (P j) ^ 2 + W z) ^ (-c')) ∂volume) ∂μ
      ≤ Kbound (m + 1) c' Tp * μ Z := by
  have hinner : ∀ z, ∫⁻ P in morseBox (m + 1) Tp, ENNReal.ofReal ((∑ j, (P j) ^ 2 + W z) ^ (-c'))
      ≤ Kbound (m + 1) c' Tp := by
    intro z
    rw [Kbound]
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

/-- The `R`-independent split-form bound `Kbound 4 c' (2T) · vol(matBox 1 4 T)`. -/
noncomputable def schurDBound (c' T : ℝ) : ℝ≥0∞ := Kbound 4 c' (2 * T) * volume (matBox 1 4 T)

/-- **`schurSplitD_lintegral`, the `≤`-form** (`R`-independent bound). Same shear-peel as the `_lt_top`
form, ending at the explicit `Kbound·vol`. Needs `hbd : |R 0 1| ≤ 1` (the box-enlarge `T → 2T`). -/
theorem schurSplitD_lintegral_le (R : Fin 2 → Fin 2 → ℝ) (Sc : Matrix (Fin 1) (Fin 1) ℝ)
    (h00 : R 0 0 = 1) (hbd : ∀ i k, |R i k| ≤ 1) (c' : ℝ) (hc0 : 0 < c') (hc' : c' < 2)
    (T : ℝ) (hT : 0 < T) :
    (∫⁻ S in matBox 2 4 T, ENNReal.ofReal ((schurSplitD R Sc S) ^ (-c'))) ≤ schurDBound c' T := by
  have hint : ∀ S : Fin 2 → Fin 4 → ℝ,
      ENNReal.ofReal ((schurSplitD R Sc S) ^ (-c'))
        = ENNReal.ofReal (((∑ j, (S 0 j + R 0 1 * S 1 j) ^ 2)
            + (Sc 0 0) ^ 2 * ∑ j, (S 1 j) ^ 2) ^ (-c')) := fun S => by rw [schurSplitD_eq R h00 Sc S]
  rw [setLIntegral_congr_fun (matBox_measurableSet 2 4 T) (fun S _ => hint S)]
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 2 => Fin 4 → ℝ) 0 with he
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin 2 => Fin 4 → ℝ) 0
  set H : (Fin 4 → ℝ) × (Fin 1 → Fin 4 → ℝ) → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (((∑ j, (q.1 j + R 0 1 * q.2 0 j) ^ 2)
      + (Sc 0 0) ^ 2 * ∑ j, (q.2 0 j) ^ 2) ^ (-c')) with hHdef
  have hHmeas : Measurable H := by
    rw [hHdef]
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    refine Measurable.add ?_ ?_
    · refine Finset.measurable_sum _ (fun j _ => (Measurable.pow_const ?_ 2))
      exact ((measurable_pi_apply j).comp measurable_fst).add (measurable_const.mul
        ((measurable_pi_apply j).comp ((measurable_pi_apply 0).comp measurable_snd)))
    · refine measurable_const.mul (Finset.measurable_sum _ (fun j _ => (Measurable.pow_const ?_ 2)))
      exact (measurable_pi_apply j).comp ((measurable_pi_apply 0).comp measurable_snd)
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
  have hLHS : (∫⁻ S in matBox 2 4 T,
      ENNReal.ofReal (((∑ j, (S 0 j + R 0 1 * S 1 j) ^ 2)
        + (Sc 0 0) ^ 2 * ∑ j, (S 1 j) ^ 2) ^ (-c')))
      = ∫⁻ q in (morseBox 4 T ×ˢ matBox 1 4 T), H q := by
    rw [hsplit, ← hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding H
        (morseBox 4 T ×ˢ matBox 1 4 T)]
    refine setLIntegral_congr_fun ?_ (fun S _ => rfl)
    exact e.measurable (MeasurableSet.prod (morseBox_measurableSet 4 T) (matBox_measurableSet 1 4 T))
  rw [hLHS, Measure.volume_eq_prod, setLIntegral_prod _ hHmeas.aemeasurable,
    lintegral_lintegral_swap hHmeas.aemeasurable, schurDBound]
  refine le_trans (setLIntegral_mono_ae' (matBox_measurableSet 1 4 T) (ae_of_all _ (fun S1 hS1 => ?_)))
    (radial_morse_dominates_absZ_le (m := 3) volume c' (by norm_num; linarith) (le_of_lt hc0)
      (2 * T) (by linarith) (fun S1 : Fin 1 → Fin 4 → ℝ => (Sc 0 0) ^ 2 * ∑ j, (S1 0 j) ^ 2)
      (fun S1 => by positivity) (matBox 1 4 T))
  set shift : Fin 4 → ℝ := fun j => R 0 1 * S1 0 j with hshift
  set f : (Fin 4 → ℝ) → ℝ≥0∞ := fun P =>
    ENNReal.ofReal (((∑ j, (P j) ^ 2) + (Sc 0 0) ^ 2 * ∑ j, (S1 0 j) ^ 2) ^ (-c')) with hf
  have hrw : ∀ row0 : Fin 4 → ℝ, H (row0, S1) = f (row0 + shift) := fun row0 => by rw [hHdef, hf]; rfl
  rw [lintegral_congr hrw]
  refine lintegral_translate_le_local 4 shift (morseBox 4 T) (morseBox 4 (2 * T)) f ?_
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

/-- N2b's `c₀` for `r = 2, j = 1`, named via `Classical.choose` so the SAME constant is used at every
angular point (the ratio residual needs a `z`-uniform bound). `R`-independent (N2b is `∃ c₀, ∀ R S`). -/
noncomputable def c0N2b : ℝ :=
  (schur_minorPivot_split (r := 2) (p := 4) 1 (by norm_num)).choose

/-- `0 < c0N2b` (the first conjunct of N2b's spec). -/
theorem c0N2b_pos : 0 < c0N2b :=
  (schur_minorPivot_split (r := 2) (p := 4) 1 (by norm_num)).choose_spec.choose_spec.1

/-- The `R`-independent inner-S bound: `ofReal(c0N2b^{−c'}) · schurDBound c' T`. -/
noncomputable def schurInnerBnd2 (c' T : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (c0N2b ^ (-c')) * schurDBound c' T

theorem schurInnerBnd2_lt_top (c' : ℝ) (hc' : c' < 2) (T : ℝ) (hT : 0 < T) :
    schurInnerBnd2 c' T < ⊤ := by
  rw [schurInnerBnd2, schurDBound]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top (Kbound_lt_top 3 (2 * T) (by linarith) c' (by norm_num; linarith))
      (matBox_volume_lt_top 1 4 T))

/-- **`schurInner_S`, the uniform `≤`-form** (pivot at `(0,0)`): `∫_S frobSq(R·S)^{−c'} ≤ schurInnerBnd2`
— the `R`-INDEPENDENT bound (`c0N2b` is N2b's fixed constant, the split-form bound `schurDBound`, both
`R`-free). Same chain as `schurInner_S_le` but ending at the explicit bound the ratio residual needs. -/
theorem schurInner_S_bound (R : Fin 2 → Fin 2 → ℝ) (h00 : R 0 0 = 1) (hbd : ∀ i k, |R i k| ≤ 1)
    (c' : ℝ) (hc0 : 0 < c') (hc' : c' < 2) (T : ℝ) (hT : 0 < T) :
    (∫⁻ S in matBox 2 4 T, ENNReal.ofReal ((frobSq (rmatMul (fun a b => R a b) S)) ^ (-c')))
      ≤ schurInnerBnd2 c' T := by
  -- N2b's witnesses via `choose` (same `c0N2b` as `schurInnerBnd2`).
  have hspec := (schur_minorPivot_split (r := 2) (p := 4) 1 (by norm_num)).choose_spec.choose_spec
  set c₁ := (schur_minorPivot_split (r := 2) (p := 4) 1 (by norm_num)).choose_spec.choose with hc₁def
  obtain ⟨hc₀, hc₁, hN2b⟩ := hspec
  have hbdM : ∀ a b : Fin 2, |(Matrix.of (fun a b => R a b)) a b| ≤ 1 := hbd
  have hpivdet : (Matrix.of (fun a b : Fin 1 =>
      (Matrix.of (fun a b => R a b)) ⟨a, lt_of_lt_of_le a.2 (by norm_num)⟩
        ⟨b, lt_of_lt_of_le b.2 (by norm_num)⟩)).det = 1 := by
    rw [Matrix.det_fin_one]; simpa using h00
  have hpivot : ∀ (I J : Fin 1 → Fin 2),
      |((Matrix.of (fun a b => R a b)).submatrix I J).det|
        ≤ |(Matrix.of (fun a b : Fin 1 =>
            (Matrix.of (fun a b => R a b)) ⟨a, lt_of_lt_of_le a.2 (by norm_num)⟩
              ⟨b, lt_of_lt_of_le b.2 (by norm_num)⟩)).det| := by
    intro I J
    rw [Matrix.det_fin_one, hpivdet, abs_one, Matrix.submatrix_apply, Matrix.of_apply]
    exact hbd (I 0) (J 0)
  have hne : (Matrix.of (fun a b : Fin 1 =>
      (Matrix.of (fun a b => R a b)) ⟨a, lt_of_lt_of_le a.2 (by norm_num)⟩
        ⟨b, lt_of_lt_of_le b.2 (by norm_num)⟩)).det ≠ 0 := by
    rw [hpivdet]; norm_num
  set RM : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of (fun a b => R a b) with hRM
  obtain ⟨Sc, hSceq, _hdet, _, _⟩ := hN2b RM (fun _ _ => 0) hbdM hpivot hne
  have hbounds : ∀ S : Fin 2 → Fin 4 → ℝ,
      c0N2b * schurSplitD R Sc S ≤ frobSq (rmatMul (fun a b => R a b) S)
        ∧ frobSq (rmatMul (fun a b => R a b) S) ≤ c₁ * schurSplitD R Sc S := by
    intro S
    obtain ⟨Sc', hSceq', _, hlo, hup⟩ := hN2b RM S hbdM hpivot hne
    have hSceq2 : Sc' = Sc := by rw [hSceq', ← hSceq]
    subst hSceq2
    exact ⟨hlo, hup⟩
  calc (∫⁻ S in matBox 2 4 T, ENNReal.ofReal ((frobSq (rmatMul (fun a b => R a b) S)) ^ (-c')))
      ≤ ENNReal.ofReal (c0N2b ^ (-c'))
          * ∫⁻ S in matBox 2 4 T, ENNReal.ofReal ((schurSplitD R Sc S) ^ (-c')) :=
        schurSplit_lintegral_le volume c0N2b c₁ c0N2b_pos
          (fun S => schurSplitD R Sc S) (fun S => frobSq (rmatMul (fun a b => R a b) S))
          (matBox 2 4 T) (fun S => schurSplitD_nonneg R Sc S) (fun S => frobSq_nonneg _)
          (fun S => (hbounds S).1) (fun S => (hbounds S).2) c' hc0
    _ ≤ ENNReal.ofReal (c0N2b ^ (-c')) * schurDBound c' T :=
        mul_le_mul_left' (schurSplitD_lintegral_le R Sc h00 hbd c' hc0 hc' T hT) _
    _ = schurInnerBnd2 c' T := by rw [schurInnerBnd2]

/-- **The uniform inner-S bound at an arbitrary pivot** (the ratio-residual plug). `R i₀ j₀ = 1`,
`|R i k| ≤ 1` ⟹ `∫_S frobSq(R·S)^{−c'} ≤ schurInnerBnd2 c' T` — the `R`-independent bound (same value at
every angular point). Swap the pivot to `(0,0)` then `schurInner_S_bound`. -/
theorem schurInner_S_bound_pivot (R : Fin 2 → Fin 2 → ℝ) (i₀ j₀ : Fin 2) (hpiv : R i₀ j₀ = 1)
    (hbd : ∀ i k, |R i k| ≤ 1) (c' : ℝ) (hc0 : 0 < c') (hc' : c' < 2) (T : ℝ) (hT : 0 < T) :
    (∫⁻ S in matBox 2 4 T, ENNReal.ofReal ((frobSq (rmatMul (fun a b => R a b) S)) ^ (-c')))
      ≤ schurInnerBnd2 c' T := by
  set σr := Equiv.swap i₀ 0 with hσr
  set σc := Equiv.swap j₀ 0 with hσc
  set R' : Fin 2 → Fin 2 → ℝ := fun r c => R (σr r) (σc c) with hR'
  have h00' : R' 0 0 = 1 := by
    show R (σr 0) (σc 0) = 1
    rw [hσr, hσc, Equiv.swap_apply_right, Equiv.swap_apply_right]; exact hpiv
  have hbd' : ∀ i k, |R' i k| ≤ 1 := fun i k => hbd (σr i) (σc k)
  have hrw : ∀ S : Fin 2 → Fin 4 → ℝ,
      ENNReal.ofReal ((frobSq (rmatMul (fun a b => R a b) S)) ^ (-c'))
        = ENNReal.ofReal ((frobSq (rmatMul (fun a b => R' a b) (fun k j => S (σc k) j))) ^ (-c')) :=
    fun S => by rw [frobSq_rmatMul_perm2 R S σr σc]
  rw [setLIntegral_congr_fun (matBox_measurableSet 2 4 T) (fun S _ => hrw S)]
  rw [← matBox24_rowperm_lintegral T σc
    (fun S => ENNReal.ofReal ((frobSq (rmatMul (fun a b => R' a b) S)) ^ (-c')))]
  exact schurInner_S_bound R' h00' hbd' c' hc0 hc' T hT

/-! ### The chart integrand factor + the per-chart finiteness + the assembly -/

/-- The chart integrand on `chartDomOn univ p`, after the indicator decouple + radial homogeneity, factors
as `radInd(y p) · innerS2`: box indicator decouples to `|y p| ≤ T` (`flatBox2_blowup_mem_iff`), loss
factors the radial scale (`gFlat2_blowup_radial`), `((y p)²)^{−c'}` peels out — combining `|y p|³` to
`|y p|^{3−2c'}`. -/
theorem chart_integrand_factor2 (c' : ℝ) (hc0 : 0 < c') (hc' : c' < 2) (T : ℝ) (hT : 0 < T)
    (p : Fin (2 * 2)) (y : Fin (2 * 2) → ℝ) (hyp0 : y p ≠ 0)
    (hy : y ∈ chartDomOn (Finset.univ : Finset (Fin (2 * 2))) p) :
    ENNReal.ofReal (|y p| ^ 3)
        * (flatBox2 T).indicator (gFlat2 c' T) (pivotBlowupOn
            (Finset.univ : Finset (Fin (2 * 2))) p y)
      = (Set.Icc (-T) T).indicator
          (fun a => ENNReal.ofReal (|a| ^ ((3 : ℝ) - 2 * c'))) (y p) * innerS2 c' T p y := by
  by_cases hmem : pivotBlowupOn (Finset.univ : Finset (Fin (2 * 2))) p y ∈ flatBox2 T
  · have hyp : |y p| ≤ T := (flatBox2_blowup_mem_iff T p y hy).1 hmem
    rw [Set.indicator_of_mem hmem,
      Set.indicator_of_mem (s := Set.Icc (-T) T) (by rw [Set.mem_Icc, ← abs_le]; exact hyp)]
    rw [gFlat2_blowup_radial c' T p y, innerS2]
    have hpull : ∀ S : Fin 2 → Fin 4 → ℝ,
        ENNReal.ofReal (((y p) ^ 2 * frobSq (rmatMul (Rmat2 p y) S)) ^ (-c'))
          = ENNReal.ofReal ((((y p) ^ 2) ^ (-c')))
            * ENNReal.ofReal ((frobSq (rmatMul (Rmat2 p y) S)) ^ (-c')) := by
      intro S
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
        ← Real.mul_rpow (by positivity) (frobSq_nonneg _)]
    rw [lintegral_congr hpull, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc]
    congr 1
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hb : ((y p) ^ 2 : ℝ) = |y p| ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    have hpos : (0 : ℝ) < |y p| := abs_pos.2 hyp0
    rw [hb, ← Real.rpow_natCast (|y p|) 3, ← Real.rpow_mul (le_of_lt hpos), ← Real.rpow_add hpos]
    congr 1; push_cast; ring
  · have hyp : ¬ |y p| ≤ T := fun h => hmem ((flatBox2_blowup_mem_iff T p y hy).2 h)
    rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (s := Set.Icc (-T) T)
        (by rw [Set.mem_Icc, ← abs_le]; exact hyp), zero_mul, mul_zero]

/-- **The per-chart finiteness.** For each `Δ`-entry pivot `p : Fin 4` and `0 < c' < 2`, the radial-blow-up
chart integral (Jacobian `|y p|³`) is finite: `chart_integrand_factor2` → `radInd(y p)·innerS2`; the
`piFinSuccAbove p` MP + Tonelli factor the pivot axis from the 3 ratios (`innerS2` is `a`-invariant); the
radial axis is `radial_aAxis_divisor_lt_top 2`-finite (`c' < 2`); the ratio residual is finite via the
UNIFORM `schurInner_S_bound_pivot` (`Rmat2` has pivot `1`, entries `≤ 1`) — `∫_z K = K·vol`. -/
theorem matBox2_chart_lt_top (c' : ℝ) (hc0 : 0 < c') (hc' : c' < 2) (T : ℝ) (hT : 0 < T)
    (p : Fin (2 * 2)) :
    ∫⁻ y in chartDomOn (Finset.univ : Finset (Fin (2 * 2))) p \ pivotZeroOn p,
        ENNReal.ofReal |(pivotBlowupOnDeriv (Finset.univ : Finset (Fin (2 * 2))) p y).det|
          * (flatBox2 T).indicator (gFlat2 c' T) (pivotBlowupOn
              (Finset.univ : Finset (Fin (2 * 2))) p y)
      < ⊤ := by
  have hdet : ∀ y : Fin (2 * 2) → ℝ,
      |(pivotBlowupOnDeriv (Finset.univ : Finset (Fin (2 * 2))) p y).det| = |y p| ^ 3 := by
    intro y
    rw [pivotBlowupOnDeriv_det (Finset.univ : Finset (Fin (2 * 2))) p (Finset.mem_univ p) y]
    simp [abs_pow]
  simp only [hdet]
  have hmsD : MeasurableSet (chartDomOn (Finset.univ : Finset (Fin (2 * 2))) p \ pivotZeroOn p) := by
    refine MeasurableSet.diff ?_ ?_
    · have heq : chartDomOn (Finset.univ : Finset (Fin (2 * 2))) p
          = ⋂ k ∈ (Finset.univ.erase p), {y : Fin (2 * 2) → ℝ | |y k| ≤ 1} := by
        ext y
        simp only [chartDomOn, Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_erase,
          Finset.mem_univ, true_and, and_true, true_implies]
      rw [heq]
      refine Finset.measurableSet_biInter (Finset.univ.erase p) (fun k _ => ?_)
      exact measurableSet_le ((measurable_pi_apply k).abs) measurable_const
    · exact (measurable_pi_apply p (measurableSet_singleton 0))
  rw [setLIntegral_congr_fun hmsD (fun y hy => chart_integrand_factor2 c' hc0 hc' T hT p y hy.2 hy.1)]
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (2 * 2) => ℝ) p with he
  have hmp : MeasurePreserving e (volume) (volume) := volume_preserving_piFinSuccAbove _ p
  have hpre : (chartDomOn (Finset.univ : Finset (Fin (2 * 2))) p \ pivotZeroOn p)
      = e ⁻¹' (({a : ℝ | a ≠ 0}) ×ˢ (Set.univ.pi (fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1))) := by
    ext y
    simp only [chartDomOn, pivotZeroOn, Set.mem_diff, Set.mem_setOf_eq, Set.mem_preimage,
      Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies, he]
    show (_ ∧ _) ↔ ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (2 * 2) => ℝ) p) y).1 ≠ 0 ∧ _
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, fun j => ?_⟩
      rw [Set.mem_Icc, ← abs_le]
      exact h1 (p.succAbove j) (Finset.mem_univ _) (Fin.succAbove_ne p j)
    · rintro ⟨h1, h2⟩
      refine ⟨fun k _ hk => ?_, h1⟩
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
      have := h2 j; rw [Set.mem_Icc, ← abs_le] at this; exact this
  have hSms : MeasurableSet
      (({a : ℝ | a ≠ 0}) ×ˢ (Set.univ.pi (fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1))) :=
    MeasurableSet.prod (by measurability) (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
  set g : (Fin (2 * 2) → ℝ) → ℝ≥0∞ := fun y =>
    (Set.Icc (-T) T).indicator (fun a => ENNReal.ofReal (|a| ^ ((3 : ℝ) - 2 * c'))) (y p)
      * innerS2 c' T p y with hgdef
  have hgmeas : Measurable g := by
    rw [hgdef]
    refine Measurable.mul ?_ (measurable_innerS2 c' T p)
    have hind : Measurable (fun a : ℝ =>
        (Set.Icc (-T) T).indicator (fun a => ENNReal.ofReal (|a| ^ ((3 : ℝ) - 2 * c'))) a) := by
      refine Measurable.indicator ?_ measurableSet_Icc
      exact ENNReal.measurable_ofReal.comp ((measurable_id.abs).pow_const _)
    exact hind.comp (measurable_pi_apply p)
  rw [hpre]
  have key := hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding (fun q => g (e.symm q))
    (({a : ℝ | a ≠ 0}) ×ˢ (Set.univ.pi (fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1)))
  have htrans : (∫⁻ y in e ⁻¹' (({a : ℝ | a ≠ 0}) ×ˢ
        (Set.univ.pi (fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1))), g y)
      = ∫⁻ q in (({a : ℝ | a ≠ 0}) ×ˢ (Set.univ.pi (fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1))),
          g (e.symm q) := by
    rw [← key]
    refine setLIntegral_congr_fun (e.measurable hSms) (fun y _ => ?_)
    rw [MeasurableEquiv.symm_apply_apply]
  rw [htrans]
  have hgsymm_meas : Measurable (fun q : ℝ × (Fin 3 → ℝ) => g (e.symm q)) :=
    hgmeas.comp e.symm.measurable
  rw [Measure.volume_eq_prod ℝ (Fin 3 → ℝ), setLIntegral_prod _ hgsymm_meas.aemeasurable]
  have hfactor : ∀ a : ℝ, ∀ z : Fin 3 → ℝ,
      g (e.symm (a, z))
        = (Set.Icc (-T) T).indicator (fun a => ENNReal.ofReal (|a| ^ ((3 : ℝ) - 2 * c'))) a
          * innerS2 c' T p (e.symm (0, z)) := by
    intro a z
    show (Set.Icc (-T) T).indicator (fun a => ENNReal.ofReal (|a| ^ ((3 : ℝ) - 2 * c')))
        ((e.symm (a, z)) p) * innerS2 c' T p (e.symm (a, z))
      = (Set.Icc (-T) T).indicator (fun a => ENNReal.ofReal (|a| ^ ((3 : ℝ) - 2 * c'))) a
          * innerS2 c' T p (e.symm (0, z))
    have hp_eq : (e.symm (a, z)) p = a := by rw [he]; simp [MeasurableEquiv.piFinSuccAbove]
    have hoff : innerS2 c' T p (e.symm (a, z)) = innerS2 c' T p (e.symm (0, z)) := by
      refine innerS2_offpivot c' T p _ _ (fun i hi => ?_)
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
      rw [he]; simp [MeasurableEquiv.piFinSuccAbove]
    rw [hp_eq, hoff]
  -- radial-axis factor finite (c' < 2 = 4/2)
  have hN3a : (∫⁻ a in Set.Icc (-T) T, ENNReal.ofReal (|a| ^ (((2:ℕ) ^ 2 : ℝ) - 1 - 2 * c'))) < ⊤ :=
    radial_aAxis_divisor_lt_top 2 (by norm_num) T hT c' (by norm_num; linarith)
  have hexp : (((2:ℕ) ^ 2 : ℝ) - 1 - 2 * c') = (3 : ℝ) - 2 * c' := by norm_num
  rw [hexp] at hN3a
  have hradfin : (∫⁻ a in {a : ℝ | a ≠ 0},
        (Set.Icc (-T) T).indicator (fun a => ENNReal.ofReal (|a| ^ ((3 : ℝ) - 2 * c'))) a) < ⊤ := by
    have hle1 : (∫⁻ a in {a : ℝ | a ≠ 0},
          (Set.Icc (-T) T).indicator (fun a => ENNReal.ofReal (|a| ^ ((3 : ℝ) - 2 * c'))) a)
        ≤ ∫⁻ a, (Set.Icc (-T) T).indicator
            (fun a => ENNReal.ofReal (|a| ^ ((3 : ℝ) - 2 * c'))) a := by
      have := lintegral_mono_set (μ := volume) (s := {a : ℝ | a ≠ 0}) (t := Set.univ)
        (Set.subset_univ _)
        (f := (Set.Icc (-T) T).indicator (fun a => ENNReal.ofReal (|a| ^ ((3 : ℝ) - 2 * c'))))
      rwa [setLIntegral_univ] at this
    have heq2 : (∫⁻ a, (Set.Icc (-T) T).indicator
          (fun a => ENNReal.ofReal (|a| ^ ((3 : ℝ) - 2 * c'))) a)
        = ∫⁻ a in Set.Icc (-T) T, ENNReal.ofReal (|a| ^ ((3 : ℝ) - 2 * c')) :=
      lintegral_indicator measurableSet_Icc _
    rw [heq2] at hle1
    exact lt_of_le_of_lt hle1 hN3a
  -- ratio residual finite via the UNIFORM bound (∫_z K = K·vol)
  have hzbox : MeasurableSet (Set.univ.pi (fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1)) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hratiofin : (∫⁻ z in (Set.univ.pi (fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1)),
        innerS2 c' T p (e.symm (0, z))) < ⊤ := by
    refine lt_of_le_of_lt
      (setLIntegral_mono_ae' hzbox (ae_of_all _ (fun z hz => ?_)) :
        (∫⁻ z in (Set.univ.pi (fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1)),
            innerS2 c' T p (e.symm (0, z)))
          ≤ ∫⁻ _z in (Set.univ.pi (fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1)), schurInnerBnd2 c' T) ?_
    · -- per z ∈ box: innerS2(e.symm(0,z)) ≤ schurInnerBnd2 via schurInner_S_bound_pivot
      simp only [Set.mem_pi, Set.mem_univ, true_implies] at hz
      rw [innerS2]
      refine schurInner_S_bound_pivot (Rmat2 p (e.symm (0, z))) (e2.symm p).1 (e2.symm p).2
        (Rmat2_pivot p (e.symm (0, z)))
        (fun i k => Rmat2_entry_le p (e.symm (0, z)) (fun kk hkk => ?_) i k) c' hc0 hc' T hT
      -- |e.symm(0,z) kk| ≤ 1 for kk ≠ p: kk = p.succAbove j, value is z j ∈ [−1,1]
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hkk
      have hval : (e.symm (0, z)) (p.succAbove j) = z j := by
        rw [he]; simp [MeasurableEquiv.piFinSuccAbove]
      rw [hval, abs_le]; exact Set.mem_Icc.1 (hz j)
    · rw [setLIntegral_const]
      refine ENNReal.mul_lt_top (schurInnerBnd2_lt_top c' hc' T hT) ?_
      have heq : (Set.univ.pi (fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1))
          = morseBox 3 1 := by rw [morseBox]
      rw [heq]; exact morseBox_volume_lt_top 3 1
  have hinner : ∀ a : ℝ,
      (∫⁻ z in (Set.univ.pi (fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1)), g (e.symm (a, z)))
        = (Set.Icc (-T) T).indicator (fun a => ENNReal.ofReal (|a| ^ ((3 : ℝ) - 2 * c'))) a
          * ∫⁻ z in (Set.univ.pi (fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1)),
              innerS2 c' T p (e.symm (0, z)) := by
    intro a
    have hradne : (Set.Icc (-T) T).indicator
        (fun a => ENNReal.ofReal (|a| ^ ((3 : ℝ) - 2 * c'))) a ≠ ⊤ := by
      rw [Set.indicator_apply]; split <;> simp [ENNReal.ofReal_ne_top]
    rw [lintegral_congr (fun z => hfactor a z), lintegral_const_mul' _ _ hradne]
  rw [lintegral_congr hinner, lintegral_mul_const' _ _ hratiofin.ne]
  exact ENNReal.mul_lt_top hradfin hratiofin

/-- **The (3,3,4) depth-2 weld, CLOSED.** `∫_Δ ∫_S frobSq(Δ·S)^{−c'} < ⊤` for `0 < c' < 2 = λ_{2,4}`, via
the Schur radial-recStep route: the `Δ`-outer integral reindexes to the `Fin 4` flat carrier
(`matBox2_outer_flat`), `recStep` covers it by the 4 max-modulus-entry charts (`gFlat2_cover_sum`), each
chart finite (`matBox2_chart_lt_top`), summed by `ENNReal.sum_lt_top`. The generic-N2b re-proof of
`core334_lt_top`'s corank-2 core — the depth-2 weld END-TO-END (inner-S `schurInner_S_bound` ⟶ outer
radial cover). -/
theorem core_schur2_lt_top (c' : ℝ) (hc0 : 0 < c') (hc' : c' < 2) (T : ℝ) (hT : 0 < T) :
    (∫⁻ Δ in matBox 2 2 T, ∫⁻ S in matBox 2 4 T,
        ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c'))) < ⊤ := by
  rw [matBox2_outer_flat c' T, gFlat2_cover_sum c' T]
  exact ENNReal.sum_lt_top.2 (fun p _ => matBox2_chart_lt_top c' hc0 hc' T hT p)

end DLNFibre.DLN.RLCT
