import DLNFibre.Core.Aoyagi.MonomialRLCT

/-!
# `Core.Aoyagi.DomainSandwich` — the born-α domain-sandwich feeder (one mechanism, ×6 instances)

The reusable born-α mechanism, F1-INDEPENDENT and network-free. The merged V-lower wire
(`rlctAt_ge_iInf_threshold_of_sandwich_cover`) consumes a per-chart sandwich that must hold
`∀ p ∈ dom c, ∀ᶠ w in 𝓝 p, cst · ∑ₖ monomialₖ² ≤ ∑ᵢ (Fᵢ∘g)²` — i.e. near EVERY point of the
compact chart domain, not merely at the blow-up center. `SurvivorSandwich.survivor_sandwich_lower`
gives it only near `0`. This module lifts it to the whole domain.

## The mechanism (pinned pnp — exact sympy + Codex, a CLEAN BOUNDED FILL)
The born-α is one self-similar recoord shear `S[0,·] = E·(radial) − d01·(residual)` giving pivot
`= E·1`: after GCD-factoring by the radial monomial `∏_d u_d^{ek₀ d}`, the loss pullback takes the
form `∑ᵢ (Fᵢ∘g)² = (∏_d u_d^{ek₀ d})² · ∑ⱼ residⱼ²` (`hpull`, a global polynomial identity — the
concrete per-chart content), and the survivor `resid i0` is a UNIT (the recoord cancels `d01·S10`,
`M[0,0] = E` exactly). "No deep {R=0}" (pnp F2) means the residual `∑ⱼ residⱼ²` never over-vanishes
on the chart domain (`hpos`, = `geoAtlas_resRank_zero_334`). Compactness of `dom` then upgrades the
pointwise positivity to a UNIFORM positive constant `cst`, and the sandwich holds near every point.

This is the SAME lemma at every S=2 type (T4–T9, corank-2 canonical T6 and corank-1 deep T8/T9 —
the pnp verified the recoord mechanism identical at both coranks): ONE feeder, six instantiations
(each supplies its own `hpull`/`hpos`), NOT six proofs. T1–T3 (S=1 smooth) supply `hpos` shear-free.

## Scope (honest)
- IN: the whole-domain sandwich from the global pullback identity + survivor-on-domain, general over
  `F`, `g`, the residual family `resid`, the survivor monomial `ek₀`. The two per-chart inputs
  (`hpull`, `hpos`) are HYPOTHESES — the honest born-α content each chart supplies.
- OUT: the per-chart pullback identity `hpull` itself (the concrete recoord-shear algebra on the real
  `coreGen ∘ chartMap`); `hpos` (`geoAtlas_resRank_zero_334`); the wire assembly over the cover.
-/

open MeasureTheory Filter Topology

namespace DLNFibre.Core.Aoyagi

variable {D Mn : ℕ}

/-- **The constant survivor family collapses to `Mn · monomial²`.** For the single-survivor
discharge (`M = 1` refracted into the wire's `Fin Mn` family as the constant family `fun _ ↦ ek₀`),
`∑ₖ (∏_d u_d^{ek₀ d})² = Mn · (∏_d u_d^{ek₀ d})²`. Generalises `SurvivorSandwich.sumSqFam_single`
(the `Fin 1` case) to the wire's `Fin Mn` family; the monomial threshold reads only the single
member `ek₀`, so the `Mn` copies are RLCT-invisible (absorbed into `cst`). -/
theorem sumSqFam_const_monomialFam (ek₀ : Fin D → ℕ) (w : Fin D → ℝ) :
    sumSqFam (monomialFam (fun _ : Fin Mn ↦ ek₀)) w
      = (Mn : ℝ) * (∏ d, (w d) ^ (ek₀ d)) ^ 2 := by
  simp only [sumSqFam, monomialFam]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The born-α domain-sandwich feeder** (F1-independent, one mechanism). Given the (global,
polynomial) chart pullback identity `∑ᵢ (Fᵢ∘g)² = (∏_d u_d^{ek₀ d})² · ∑ⱼ residⱼ²` (`hpull`) and
the "no deep {R=0}" survivor-present condition on a compact domain `dom` (`∑ⱼ residⱼ² > 0` throughout
`dom` — `geoAtlas_resRank_zero_334`), there is a POSITIVE `cst` for which the wire's per-chart
sandwich holds near EVERY `p ∈ dom`:
`0 ≤ cst · ∑ₖ monomialₖ²` and `cst · ∑ₖ monomialₖ² ≤ ∑ᵢ (Fᵢ∘g)²` (over the constant survivor
family). This is exactly `rlctAt_ge_iInf_threshold_of_sandwich_cover`'s `hsandwich` field for one
chart. `cst` is uniform via compactness (the continuous positive residual attains a positive min on
`dom`). -/
theorem sandwich_on_domain_of_survivor
    {ι' : Type*} [Fintype ι']
    {F : Fin Mn → (Fin D → ℝ) → ℝ} {g : (Fin D → ℝ) → (Fin D → ℝ)}
    {ek₀ : Fin D → ℕ} {resid : ι' → (Fin D → ℝ) → ℝ} {dom : Set (Fin D → ℝ)}
    (hMn : 0 < Mn)
    (hcont : ∀ i, Continuous (resid i))
    (hpull : ∀ w, sumSqFam (fun i ↦ F i ∘ g) w
        = (∏ d, (w d) ^ (ek₀ d)) ^ 2 * ∑ i, (resid i w) ^ 2)
    (hdomcpt : IsCompact dom) (hdom_ne : dom.Nonempty)
    (hpos : ∀ p ∈ dom, 0 < ∑ i, (resid i p) ^ 2) :
    ∃ cst : ℝ, 0 < cst ∧ ∀ p ∈ dom, ∀ᶠ w in 𝓝 p,
      0 ≤ cst * sumSqFam (monomialFam (fun _ : Fin Mn ↦ ek₀)) w ∧
        cst * sumSqFam (monomialFam (fun _ : Fin Mn ↦ ek₀)) w
          ≤ sumSqFam (fun i ↦ F i ∘ g) w := by
  classical
  have hRcont : Continuous (fun w ↦ ∑ i, (resid i w) ^ 2) :=
    continuous_finset_sum _ (fun i _ ↦ (hcont i).pow 2)
  obtain ⟨p₀, hp₀dom, hp₀min⟩ := hdomcpt.exists_isMinOn hdom_ne hRcont.continuousOn
  have hmpos : 0 < ∑ i, (resid i p₀) ^ 2 := hpos p₀ hp₀dom
  refine ⟨(∑ i, (resid i p₀) ^ 2) / (2 * Mn), by positivity, ?_⟩
  intro p hp
  have hp₀le : (∑ i, (resid i p₀) ^ 2) ≤ ∑ i, (resid i p) ^ 2 := isMinOn_iff.mp hp₀min p hp
  have hlt : (∑ i, (resid i p₀) ^ 2) / 2 < ∑ i, (resid i p) ^ 2 := by linarith
  have hcaR : Tendsto (fun w ↦ ∑ i, (resid i w) ^ 2) (𝓝 p)
      (𝓝 (∑ i, (resid i p) ^ 2)) := hRcont.continuousAt
  have hev : ∀ᶠ w in 𝓝 p, (∑ i, (resid i p₀) ^ 2) / 2 < ∑ i, (resid i w) ^ 2 :=
    hcaR.eventually (eventually_gt_nhds hlt)
  filter_upwards [hev] with w hw
  rw [sumSqFam_const_monomialFam, hpull w]
  set mon : ℝ := (∏ d, (w d) ^ (ek₀ d)) ^ 2 with hmondef
  have hmon : 0 ≤ mon := sq_nonneg _
  have hMnR : (0 : ℝ) < (Mn : ℝ) := by exact_mod_cast hMn
  have hkey : (∑ i, (resid i p₀) ^ 2) / (2 * Mn) * ((Mn : ℝ) * mon)
      = ((∑ i, (resid i p₀) ^ 2) / 2) * mon := by
    field_simp
  have hcst0 : (0 : ℝ) ≤ (∑ i, (resid i p₀) ^ 2) / (2 * Mn) := by positivity
  refine ⟨mul_nonneg hcst0 (mul_nonneg (le_of_lt hMnR) hmon), ?_⟩
  rw [hkey]
  nlinarith [mul_nonneg hmon (sub_nonneg.mpr (le_of_lt hw))]

/-! ## STEP 5 — the `monomialThreshold → ½·chartMin` value conversion

The wire concludes `⨅_c monomialThreshold_c ≤ rlctAt`. To read the headline value, the boxed
threshold `monomialThreshold = ⨅_{binding} (jac_d+1)/(2·kexp_d)` must be turned into half the
integer divisor minimum `chartMin = ⨅_{binding} (jac_d+1)`. Under the DLN normal-crossing fact that
each binding divisor has unit multiplicity `kexp d = 1` (worked.tex:495), the collapse is exact. -/

/-- **STEP 5 per-chart: `monomialThreshold = ½·chartMin` under unit multiplicity.** With the divisor
carrying `kexp d = 1` on its binding axes, `⨅_{binding} (jac_d+1)/(2·kexp_d) = (⨅_{binding}(jac_d+1))/2`
— half the chart's integer divisor minimum `chartMin`. -/
theorem monomialThreshold_eq_half_inf' {D : ℕ} (kexp jac : Fin D → ℕ)
    (hbind : (bindingAxes kexp).Nonempty) (hunit : ∀ d ∈ bindingAxes kexp, kexp d = 1) :
    monomialThreshold kexp jac hbind
      = (bindingAxes kexp).inf' hbind (fun d ↦ (jac d + 1 : ℝ)) / 2 := by
  have hfun : ∀ d ∈ bindingAxes kexp,
      (jac d + 1 : ℝ) / (2 * kexp d) = (jac d + 1 : ℝ) / 2 := by
    intro d hd; rw [hunit d hd]; norm_num
  rw [monomialThreshold, Finset.inf'_congr hbind rfl hfun]
  exact (Finset.comp_inf'_eq_inf'_comp hbind (· / 2)
      (fun x y ↦ (min_div_div_right (by norm_num : (0 : ℝ) ≤ 2) x y).symm)).symm

/-- **STEP 5 over the chart family: `⨅_c monomialThreshold_c = ½·divisorMin`.** Pulls the per-chart
collapse (`monomialThreshold_eq_half_inf'`) through the outer `min` over the atlas: the wire's
`⨅_c monomialThreshold (kexp c) (jac c)` equals `(⨅_c chartMin_c)/2`, so a `divisorMin = 8`
(Object D / `minAdm ![3,3,4] = 8`) reads off `⨅_c monomialThreshold_c = 4`. -/
theorem inf'_monomialThreshold_eq_half_divisorMin {ι : Type*} {D : ℕ} (s : Finset ι)
    (hs : s.Nonempty) (kexp jac : ι → Fin D → ℕ)
    (hbind : ∀ c, (bindingAxes (kexp c)).Nonempty)
    (hunit : ∀ c, ∀ d ∈ bindingAxes (kexp c), kexp c d = 1) :
    s.inf' hs (fun c ↦ monomialThreshold (kexp c) (jac c) (hbind c))
      = (s.inf' hs
          (fun c ↦ (bindingAxes (kexp c)).inf' (hbind c) (fun d ↦ (jac c d + 1 : ℝ)))) / 2 := by
  rw [Finset.inf'_congr hs rfl
      (fun c _ ↦ monomialThreshold_eq_half_inf' (kexp c) (jac c) (hbind c) (hunit c))]
  exact (Finset.comp_inf'_eq_inf'_comp hs (· / 2)
      (fun x y ↦ (min_div_div_right (by norm_num : (0 : ℝ) ≤ 2) x y).symm)).symm

-- Forced axiom gate: the born-α feeder + STEP 5 conversion rest only on
-- `[propext, Classical.choice, Quot.sound]`.
#assert_banked_clean_batch [sumSqFam_const_monomialFam, sandwich_on_domain_of_survivor,
  monomialThreshold_eq_half_inf', inf'_monomialThreshold_eq_half_divisorMin]

end DLNFibre.Core.Aoyagi
