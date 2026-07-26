import DLNFibre.DLN.Aoyagi.SurvivorFanCover
import DLNFibre.Core.Aoyagi.ChartValueLower

/-!
# R3 value brick (i)(a) — `leafPullback_sandwich`: the survivor → R>0-sandwich lower half

Fresh from R2 (`SurvivorFanCover.sumSq_residual`), F1-INDEPENDENT: the loss-pullback identity
`K = monomial² · R` is kept an OPEN hypothesis (`hpull`), never discharged via the retired α-atlas
(`leafPullback_geoAtlasNorm` / `chartBridgeFaithful_buildTree`, which carry `sorryAx`). Given a KEPT
survivor — `R = ∑ᵢ fᵢ²` a SUM of squares (G1, never a product) with the kept pivot `f i0` continuous
at `0` and `f i0 0 = 1` — the loss dominates a positive multiple of the (single, DOMINANT) survivor
monomial² near `0`. That is exactly the `hsandwich` lower half `chart_rlct_ge_half_chartMin` (i)(b)
consumes.

## Why the SINGLE survivor monomial (G1, k = 1)
The FULL-family lower bound `c · ∑ₖ monomialₖ² ≤ K` is FALSE — the non-survivor ratios `fₖ` vanish
at the blow-up center. But the RLCT value is set by the DOMINANT (divisibility-minimal) monomial, so
the sandwich is discharged at the single-survivor family `M = 1`. This is the elder's "k = 1 via the
kept-survivor SUM": we lower-bound the SUM `R = ∑ᵢ fᵢ²` by the kept survivor's square
(`SurvivorFanCover.sumSq_residual` / `Finset.single_le_sum`), never reading `R` as a product. A
binding branch with NO survivor would force `k ≥ 2` and undercut `½·chartMin`; the discharge of
`hpull` at such deep `{R=0}`-approaching leaves is the `#172` recursion — the WIRE's job, not this
per-chart atom's.

## Scope (honest)
- IN: the sandwich lower half from the survivor normal form (F1-independent, GENERAL chart —
  abstract over `K`, the residual family `f`, the survivor index `i0`, the monomial exponent `ek₀`).
- OUT: the pullback identity `K = monomial²·R` itself (OPEN `hpull`, discharged by the real chart
  algebra / `#172` recursion — the wire); the per-chart value bound (i)(b),
  `chart_rlct_ge_half_chartMin`; the V-lower cover wire over all buildTree leaves.

## Main results
- `survivor_sandwich_lower` — the survivor normal form gives `¼·monomial² ≤ K` near `0`.
- `sumSqFam_single` — the single-family bridge: `sumSqFam (monomialFam (fun _ ↦ ek₀)) = monomial²`.
- `chart_rlct_ge_half_of_survivor` — the wire-ready per-chart bound `chartMin ≤ 2·wrlctAt W K 0`
  from the survivor (chains (i)(a) into (i)(b); `hnull`/`hbdd` stay the wire's).
- `witness_survivor_sandwich` — non-vacuity (`D = 1`, `K = u₀²`, kept pivot `≡ 1`).
-/

open MeasureTheory Filter Topology
open DLNFibre.Core.Aoyagi

namespace DLNFibre.DLN.Aoyagi.SurvivorFanCover

variable {D : ℕ}

/-- **(i)(a) the survivor → sandwich lower half.** With the loss-pullback identity
`K = (∏_d u_d^{ek₀ d})² · ∑ᵢ (fᵢ)²` near `0` (OPEN — the geometric pullback, F1-independent) and a
kept survivor `f i0` continuous at `0` with `f i0 0 = 1`, the loss dominates `¼·monomial²` near `0`:
`0 ≤ ¼·monomial²` and `¼·monomial² ≤ K`. G1: `R = ∑ᵢ (fᵢ)²` is a SUM of squares, lower-bounded by
the kept pivot's square (`Finset.single_le_sum`, the `sumSq_residual` structure), which is `≥ ¼`
near `0` by continuity. This is the `hsandwich` lower half of `chart_rlct_ge_half_chartMin` at the
single-survivor family (`c = ¼`). -/
theorem survivor_sandwich_lower
    {ι' : Type*} [Fintype ι']
    {K : (Fin D → ℝ) → ℝ} {f : ι' → (Fin D → ℝ) → ℝ} {i0 : ι'} {ek₀ : Fin D → ℕ}
    (hf0 : f i0 0 = 1) (hf_cont : ContinuousAt (f i0) 0)
    (hpull : ∀ᶠ u in 𝓝 (0 : Fin D → ℝ),
      K u = (∏ d, (u d) ^ (ek₀ d)) ^ 2 * ∑ i, (f i u) ^ 2) :
    ∀ᶠ u in 𝓝 (0 : Fin D → ℝ),
      0 ≤ (1 / 4 : ℝ) * (∏ d, (u d) ^ (ek₀ d)) ^ 2 ∧
      (1 / 4 : ℝ) * (∏ d, (u d) ^ (ek₀ d)) ^ 2 ≤ K u := by
  have hev : ∀ᶠ u in 𝓝 (0 : Fin D → ℝ), (1 : ℝ) / 2 < f i0 u := by
    have htend : Tendsto (f i0) (𝓝 0) (𝓝 (f i0 0)) := hf_cont
    rw [hf0] at htend
    exact htend.eventually (eventually_gt_nhds (by norm_num : (1 : ℝ) / 2 < 1))
  filter_upwards [hpull, hev] with u hpu hgt
  have hpos : (0 : ℝ) ≤ (∏ d, (u d) ^ (ek₀ d)) ^ 2 := sq_nonneg _
  have hsq : (1 : ℝ) / 4 ≤ (f i0 u) ^ 2 := by
    have h12 : (1 : ℝ) / 2 ≤ f i0 u := le_of_lt hgt
    nlinarith [h12, sq_nonneg (f i0 u - 1 / 2)]
  have hle : (f i0 u) ^ 2 ≤ ∑ i, (f i u) ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg (f i u)) (Finset.mem_univ i0)
  have hR : (1 : ℝ) / 4 ≤ ∑ i, (f i u) ^ 2 := le_trans hsq hle
  refine ⟨by positivity, ?_⟩
  rw [hpu]
  nlinarith [mul_nonneg hpos (sub_nonneg.mpr hR)]

/-- The single-family bridge: `sumSqFam (monomialFam (fun _ : Fin 1 ↦ ek₀)) u = (∏_d u_d^{ek₀ d})²`.
Lets `survivor_sandwich_lower` feed `chart_rlct_ge_half_chartMin` at `M = 1` (the dominant survivor
monomial), whose weighted-RLCT value is `min over binding axes of (jac_d + 1) = chartMin`. -/
theorem sumSqFam_single (ek₀ : Fin D → ℕ) (u : Fin D → ℝ) :
    sumSqFam (monomialFam (fun _ : Fin 1 ↦ ek₀)) u = (∏ d, (u d) ^ (ek₀ d)) ^ 2 := by
  simp [sumSqFam, monomialFam]

/-- **The wire-ready per-chart value bound from a survivor** (chains (i)(a) into (i)(b),
F1-independent). With the chart's Jacobian weight `W = jacWeight h · unit` (unit cts/nonzero/
measurable at `0`), the unit divisor multiplicity `ek₀ d = 1` on binding axes, and the loss-pullback
`K = monomial² · ∑ᵢ (fᵢ)²` with a kept survivor (`f i0` cts, `f i0 0 = 1`), the per-chart weighted
RLCT satisfies `chartMin ≤ 2 · wrlctAt W K 0`, `chartMin = ⨅ over binding axes of (h_d + 1)`. The
`hsandwich` is discharged internally by `survivor_sandwich_lower` at the single-survivor family
(`M = 1`, `c = ¼`); `hnull` (the `{monomial=0}` null guard) and `hbdd` stay hypotheses the cover
WIRE discharges (`locallyNullZeros_sumSqFam_monomialFam`). This is the V-lower per-chart atom the
wire quantifies over ALL buildTree leaves (elder watch-item: genuinely general — any `ek₀`, `h`,
`unit`, survivor). -/
theorem chart_rlct_ge_half_of_survivor
    {ι' : Type*} [Fintype ι']
    {W K unit : (Fin D → ℝ) → ℝ} {f : ι' → (Fin D → ℝ) → ℝ} {i0 : ι'} {ek₀ h : Fin D → ℕ}
    (hbind : (bindingAxes ek₀).Nonempty)
    (hunit1 : ∀ d ∈ bindingAxes ek₀, ek₀ d = 1)
    (hunit : ContinuousAt unit 0) (hunit0 : unit 0 ≠ 0) (hunitmeas : Measurable unit)
    (hW : ∀ᶠ u in 𝓝 (0 : Fin D → ℝ), W u = jacWeight h u * unit u)
    (hWmeas : Measurable W) (hKmeas : Measurable K)
    (hWnonneg : ∀ᶠ u in 𝓝 (0 : Fin D → ℝ), 0 ≤ W u)
    (hf0 : f i0 0 = 1) (hf_cont : ContinuousAt (f i0) 0)
    (hpull : ∀ᶠ u in 𝓝 (0 : Fin D → ℝ),
      K u = (∏ d, (u d) ^ (ek₀ d)) ^ 2 * ∑ i, (f i u) ^ 2)
    (hnull : LocallyNullZeros
      (fun u ↦ (1 / 4 : ℝ) * sumSqFam (monomialFam (fun _ : Fin 1 ↦ ek₀)) u) 0)
    (hbdd : BddAbove (wLocalAdmissibleExponents W K 0)) :
    (bindingAxes ek₀).inf' hbind (fun d ↦ (h d + 1 : ℝ)) ≤ 2 * wrlctAt W K 0 := by
  have hsw : ∀ᶠ u in 𝓝 (0 : Fin D → ℝ),
      0 ≤ (1 / 4 : ℝ) * sumSqFam (monomialFam (fun _ : Fin 1 ↦ ek₀)) u ∧
      (1 / 4 : ℝ) * sumSqFam (monomialFam (fun _ : Fin 1 ↦ ek₀)) u ≤ K u := by
    filter_upwards [survivor_sandwich_lower hf0 hf_cont hpull] with u hu
    rw [sumSqFam_single]; exact hu
  exact chart_rlct_ge_half_chartMin (e := fun _ : Fin 1 ↦ ek₀) (k₀ := 0) (c := 1 / 4)
    (by norm_num) (fun _ _ ↦ le_refl _) hbind hunit1 hunit hunit0 hunitmeas hW hWmeas hKmeas
    hWnonneg hsw hnull hbdd

/-- Non-vacuity: `D = 1`, loss `K u = (u 0)²`, single residual entry `f ≡ 1` (its own kept pivot,
continuous, value `1` at `0`), monomial exponent `ek₀ = ![1]` (so `∏_d u_d^{ek₀ d} = u 0`). The
sandwich fires: `¼·(u 0)² ≤ (u 0)²` near `0`. -/
theorem witness_survivor_sandwich :
    ∀ᶠ u in 𝓝 (0 : Fin 1 → ℝ),
      0 ≤ (1 / 4 : ℝ) * (∏ d, (u d) ^ (![1] : Fin 1 → ℕ) d) ^ 2 ∧
      (1 / 4 : ℝ) * (∏ d, (u d) ^ (![1] : Fin 1 → ℕ) d) ^ 2 ≤ (u 0) ^ 2 := by
  refine survivor_sandwich_lower (f := fun (_ : Fin 1) (_ : Fin 1 → ℝ) => (1 : ℝ)) (i0 := 0)
    rfl continuousAt_const ?_
  filter_upwards with u
  simp

/-- **Non-vacuity of `chart_rlct_ge_half_chartMin` (i)(b), in-file witness** (reviewer/Codex
instance, the bedrock "witness shown" bar). `D = M = 1`, `e = ![![1]]` (`e₀₀ = 1`), `h = 0`,
`c = 1`, `W = unit ≡ 1`, `K = ∑ₖ monomialₖ² = (u 0)²`: ALL hypotheses discharge (hbdd via
`monomialSumSq_wLocalAdmissible_eq` + `bddAbove_Ico`; hnull via `Measure.pi_hyperplane` on the
codim-1 zero set `{u 0 = 0}`), so the theorem fires — `1 ≤ 2·wrlctAt` (the RLCT of `u²` is `½`, so
the bound holds with equality `1 = 2·½`). -/
example :
    (bindingAxes ((![![1]] : Fin 1 → Fin 1 → ℕ) 0)).inf'
        (by decide : (bindingAxes ((![![1]] : Fin 1 → Fin 1 → ℕ) 0)).Nonempty)
        (fun d ↦ ((0 : Fin 1 → ℕ) d + 1 : ℝ))
      ≤ 2 * wrlctAt (fun _ ↦ (1 : ℝ))
          (sumSqFam (monomialFam (![![1]] : Fin 1 → Fin 1 → ℕ))) 0 := by
  have hW : ∀ᶠ u in 𝓝 (0 : Fin 1 → ℝ),
      (fun _ ↦ (1 : ℝ)) u = jacWeight (0 : Fin 1 → ℕ) u * (fun _ ↦ (1 : ℝ)) u :=
    Filter.Eventually.of_forall (fun u ↦ by simp [jacWeight])
  refine chart_rlct_ge_half_chartMin (e := (![![1]] : Fin 1 → Fin 1 → ℕ)) (k₀ := 0) (c := 1)
    one_pos (by decide) (by decide) (by decide)
    continuousAt_const one_ne_zero measurable_const hW measurable_const ?_
    (Filter.Eventually.of_forall (fun _ ↦ zero_le_one))
    (Filter.Eventually.of_forall (fun u ↦ ⟨by rw [one_mul]; exact sumSqFam_nonneg _ u, by
      rw [one_mul]⟩)) ?_ ?_
  · -- `K = ∑ₖ monomialₖ²` is measurable (finite sum of squares of monomials)
    unfold sumSqFam monomialFam; fun_prop
  · -- hnull: `{1·∑monomialₖ² = 0} = {u 0 = 0}` is codim-1, Lebesgue-null
    refine ⟨Set.univ, Filter.univ_mem, ?_⟩
    have hset : {u : Fin 1 → ℝ | (fun u ↦ (1 : ℝ) *
        sumSqFam (monomialFam (![![1]] : Fin 1 → Fin 1 → ℕ)) u) u = 0} ∩ Set.univ
        = {u : Fin 1 → ℝ | u 0 = 0} := by
      ext u
      simp [sumSqFam, monomialFam, pow_eq_zero_iff]
    rw [hset, volume_pi]
    exact Measure.pi_hyperplane _ 0 0
  · -- hbdd: the weighted-admissible set is `Ico 0 (monomialThreshold …)`, hence bounded above
    have heq := monomialSumSq_wLocalAdmissible_eq (e := (![![1]] : Fin 1 → Fin 1 → ℕ))
      (h := (0 : Fin 1 → ℕ)) (k₀ := (0 : Fin 1)) (W := fun _ ↦ (1 : ℝ)) (unit := fun _ ↦ (1 : ℝ))
      (by decide) (by decide) continuousAt_const one_ne_zero measurable_const hW
    rw [heq]; exact bddAbove_Ico

-- Forced axiom gate: rests only on `[propext, Classical.choice, Quot.sound]`.
#assert_banked_clean_batch [survivor_sandwich_lower, sumSqFam_single,
  chart_rlct_ge_half_of_survivor, witness_survivor_sandwich]

end DLNFibre.DLN.Aoyagi.SurvivorFanCover
