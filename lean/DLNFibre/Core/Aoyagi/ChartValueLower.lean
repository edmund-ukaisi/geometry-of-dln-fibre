import DLNFibre.Core.Aoyagi.MonomialRLCT

/-!
# `DLNFibre.Core.Aoyagi.ChartValueLower` — the per-chart R>0-SANDWICH RLCT lower bound

R3 value-side brick (i)(b): the abstract per-chart RLCT LOWER bound, taking the R>0 SANDWICH as a
HYPOTHESIS (F1-INDEPENDENT — no `LeafPullback`/`ChartBridgeFaithful` dependence). It is the V-lower
content the reroute value spine needs, isolated from the (gated) `leafPullback_sandwich` (i)(a).

## The sandwich → the lower bound
On a chart with Jacobian weight `W = jacWeight h · unit` (unit continuous, nonvanishing at 0), if
the pulled-back loss `K` DOMINATES a positive multiple of the monomial sum-of-squares near 0 —
`c · ∑ₖ (monomialₖ)² ≤ K`, `c > 0` (the sandwich's lower half: `K = monomial²·R`, `R ≥ (kept)² ≥ c`
by `SurvivorFanCover.sumSq_residual` + continuity of the kept "1"-pivot; G1: `R` a SUM of squares,
NOT a product) — then the per-chart weighted RLCT is bounded below by `½·chartMin`:
`chartMin ≤ 2 · wrlctAt W K 0`, `chartMin = min over binding axes of (jacᵈ + 1)`.

Pure composition of banked engine machinery: `monomialSumSq_two_mul_wrlctAt_eq_min` (the monomial
value `2·wrlctAt = min binding (h+1)`), `wrlctAt_const_mul` (the `c·` rescale is RLCT-invisible),
`wrlctAt_mono_of_eventually_le` (a larger integrand raises the weighted RLCT). The `{monomial=0}`
null-guard is a hypothesis here (discharged downstream by the Core poly-null brick
`MvPolynomial.volume_zeroSet_eq_zero`).

## Scope
- IN: the abstract per-chart R>0-sandwich lower bound (sandwich + monomial value as hypotheses).
- OUT (gated / separate): `leafPullback_sandwich` (i)(a) — that the REAL `loss∘g` on the flatCube
  pivotChart leaf HAS this sandwich form. It must DISCHARGE `LeafPullback` (the DEFINITION, a faithful
  sandwich spec — kept OPEN) via the FRESH pivotChart BLOW-UP sandwich (`SurvivorFanCover.sumSq_residual`
  + #172 + a Morse baseForm), NEVER via `ChartBridgeFaithful` (the F1-holed det-1 discharge, carries
  `sorryAx` — F1 check 2026-07-26, charter §3 tripwire); gate it: `#print axioms` clean-three, no route
  through {`leafPullback_geoAtlasNorm`, `chartBridgeFaithful_buildTree`, `leafDiagFrob_geoAtlasNorm`}.
  Then the V-lower WIRE over the cover (`rlctAt_sumSqFam_eq_iInf_charts`); G2 superadditivity (general-d).

## Main result
- `chart_rlct_ge_half_chartMin` — `chartMin ≤ 2 · wrlctAt W K 0` from the R>0 sandwich lower half.
-/

open MeasureTheory Filter Topology

namespace DLNFibre.Core.Aoyagi

variable {D M : ℕ}

/-- **The per-chart R>0-sandwich RLCT lower bound (F1-independent).** With the chart's Jacobian
weight `W = jacWeight h · unit` (unit cts/nonzero/measurable at 0) and the loss `K` over a positive
multiple of the monomial sum-of-squares near 0 (`c · ∑ₖ monomialₖ² ≤ K`, `c > 0` — the
sandwich lower half, `K = monomial²·R` with `R ≥ c`), the per-chart weighted RLCT satisfies
`chartMin ≤ 2 · wrlctAt W K 0`, `chartMin = ⨅ over binding axes of (jacᵈ + 1)`. The `≥`-half of the
per-chart value; feeds the V-lower cover wire. -/
theorem chart_rlct_ge_half_chartMin
    {W K unit : (Fin D → ℝ) → ℝ} {e : Fin M → Fin D → ℕ} {h : Fin D → ℕ} {k₀ : Fin M} {c : ℝ}
    (hc : 0 < c)
    (hchain : ∀ k d, e k₀ d ≤ e k d) (hbind : (bindingAxes (e k₀)).Nonempty)
    (hunit1 : ∀ d ∈ bindingAxes (e k₀), e k₀ d = 1)
    (hunit : ContinuousAt unit 0) (hunit0 : unit 0 ≠ 0) (hunitmeas : Measurable unit)
    (hW : ∀ᶠ u in 𝓝 (0 : Fin D → ℝ), W u = jacWeight h u * unit u)
    (hWmeas : Measurable W) (hKmeas : Measurable K)
    (hWnonneg : ∀ᶠ u in 𝓝 (0 : Fin D → ℝ), 0 ≤ W u)
    (hsandwich : ∀ᶠ u in 𝓝 (0 : Fin D → ℝ),
      0 ≤ c * sumSqFam (monomialFam e) u ∧ c * sumSqFam (monomialFam e) u ≤ K u)
    (hnull : LocallyNullZeros (fun u ↦ c * sumSqFam (monomialFam e) u) 0)
    (hbdd : BddAbove (wLocalAdmissibleExponents W K 0)) :
    (bindingAxes (e k₀)).inf' hbind (fun d ↦ (h d + 1 : ℝ)) ≤ 2 * wrlctAt W K 0 := by
  have hval : 2 * wrlctAt W (sumSqFam (monomialFam e)) 0
      = (bindingAxes (e k₀)).inf' hbind (fun d ↦ (h d + 1 : ℝ)) :=
    monomialSumSq_two_mul_wrlctAt_eq_min hchain hbind hunit1 hunit hunit0 hunitmeas hW
  have hmono : wrlctAt W (fun u ↦ c * sumSqFam (monomialFam e) u) 0 ≤ wrlctAt W K 0 :=
    wrlctAt_mono_of_eventually_le hWmeas hKmeas hWnonneg hsandwich hnull hbdd
  have hrescale : wrlctAt W (fun u ↦ c * sumSqFam (monomialFam e) u) 0
      = wrlctAt W (sumSqFam (monomialFam e)) 0 := wrlctAt_const_mul hc
  rw [← hval, ← hrescale]
  exact mul_le_mul_of_nonneg_left hmono (by norm_num)

-- Forced axiom gate: rests only on `[propext, Classical.choice, Quot.sound]`.
#assert_banked_clean_batch [chart_rlct_ge_half_chartMin]

end DLNFibre.Core.Aoyagi
