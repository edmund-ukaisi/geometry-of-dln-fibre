import DLNFibre.Core.Analysis.RLCT.Local
import DLNFibre.Core.Analysis.RLCT.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# `RLCT.LocalMono` — B2: down-set + germ-monotonicity for `localAdmissibleExponents`

The **local analogues** of the regional monotonicity lemmas of `RLCT.Integrability`
(`admissibleExponents_downward` / `admissibleExponents_subset_of_le`), stated for the germ-level
`localAdmissibleExponents K x` (`RLCT.Local`). The proofs mirror the regional ones through
`IntegrableAtFilter`: a witnessing neighbourhood is shrunk to an **open** (hence measurable)
neighbourhood, intersected with the germ region where the domination bound holds, and integrability
descends by `Integrable.mono'`.

* **`localAdmissibleExponents_downward`** — the admissible set is a **down-set**: `0 ≤ c' ≤ c`,
  `c` admissible ⟹ `c'` admissible, when `0 ≤ K ≤ 1` *near* `x` (the germ analogue of the regional
  `hK0`/`hK1`). Then `K^(-c') ≤ K^(-c)` pointwise near `x` (a less-negative exponent, base in
  `[0,1]`), so `K^(-c')` is dominated by the locally-integrable `K^(-c)`. For a continuous germ with
  a zero at `x` (the pole regime), `0 ≤ K ≤ 1` near `x` holds automatically. The `c' = 0` case is
  `zero_mem_localAdmissibleExponents`.
* **`localAdmissibleExponents_subset_of_le`** — **germ-monotonicity in the germ**: if `K ≤ K'` near
  `x` with `K` strictly positive there, every exponent locally admissible for `K` is locally
  admissible for `K'` (a larger base with a nonpositive exponent gives a smaller value, so `K'^(-c)`
  is dominated by the integrable `K^(-c)`).

Both take the germ bounds as a **filter-eventual** hypothesis (`∀ᶠ y in 𝓝 x, …`) — the honest,
minimal germ-level form of the regional pointwise hypotheses; disclosed, not hidden.

Bare Mathlib-mirror namespace `RLCT` (network-free).
-/

open MeasureTheory Set Filter Topology

namespace RLCT

variable {n : ℕ}

/-- The constant germ `1` is locally integrable at any point of `ℝⁿ` (a small open ball has finite
measure). Used to discharge the `c = 0` base case of the down-set. -/
lemma integrableAtFilter_one_nhds (x : Fin n → ℝ) :
    IntegrableAtFilter (fun _ ↦ (1 : ℝ)) (𝓝 x) := by
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩
  exact integrableOn_const measure_ball_lt_top.ne

/-- **B2 — the down-set (domination) property, local form.** If `c` is locally admissible at `x`
and `0 ≤ c' ≤ c`, then `c'` is locally admissible, provided `0 ≤ K ≤ 1` on some neighbourhood of `x`
(`hbound`, the germ analogue of the regional `0 ≤ K ≤ 1`): there `K^(-c') ≤ K^(-c)` pointwise, so
`K^(-c')` is dominated by the locally-integrable `K^(-c)`. Needs `K` measurable for the dominated
function's strong measurability. -/
theorem localAdmissibleExponents_downward {K : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hKmeas : Measurable K) (hbound : ∀ᶠ y in 𝓝 x, 0 ≤ K y ∧ K y ≤ 1)
    {c c' : ℝ} (hc : c ∈ localAdmissibleExponents K x) (hc'0 : 0 ≤ c') (hcc' : c' ≤ c) :
    c' ∈ localAdmissibleExponents K x := by
  rcases eq_or_lt_of_le hc'0 with hc'eq | hc'pos
  · -- `c' = 0`: the constant germ `1` is locally integrable at `x`.
    rw [← hc'eq]; exact zero_mem_localAdmissibleExponents (integrableAtFilter_one_nhds x)
  refine ⟨hc'0, ?_⟩
  have hc0 : 0 < c := lt_of_lt_of_le hc'pos hcc'
  obtain ⟨s, hs, hsint⟩ := hc.2
  -- Shrink `s` and the bound region to OPEN (measurable) neighbourhoods, intersect.
  obtain ⟨s₀, hs₀s, hs₀open, hxs₀⟩ := mem_nhds_iff.1 hs
  obtain ⟨t₀, ht₀bound, ht₀open, hxt₀⟩ := eventually_nhds_iff.1 hbound
  refine ⟨s₀ ∩ t₀, (hs₀open.inter ht₀open).mem_nhds ⟨hxs₀, hxt₀⟩, ?_⟩
  have hmeas : MeasurableSet (s₀ ∩ t₀) := (hs₀open.inter ht₀open).measurableSet
  have hdom : IntegrableOn (negPow K c) (s₀ ∩ t₀) :=
    hsint.mono_set ((inter_subset_left).trans hs₀s)
  refine Integrable.mono' hdom (measurable_negPow hKmeas c').aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem hmeas (fun y hy ↦ ?_)
  obtain ⟨hKy0, hKy1⟩ := ht₀bound y hy.2
  rw [Real.norm_eq_abs, abs_of_nonneg (negPow_nonneg hKy0 c')]
  simp only [negPow_apply]
  rcases eq_or_lt_of_le hKy0 with hKyeq | hKypos
  · -- `K y = 0`: both `0^(-c') = 0` and `0^(-c) = 0` (`c', c > 0`).
    rw [← hKyeq, Real.zero_rpow (by linarith : -c' ≠ 0), Real.zero_rpow (by linarith : -c ≠ 0)]
  · -- `0 < K y ≤ 1`: a less-negative exponent gives the smaller value.
    exact Real.rpow_le_rpow_of_exponent_ge hKypos hKy1 (by linarith)

/-- **B2 — germ-monotonicity in the germ, local form.** If `K ≤ K'` near `x` with `K` strictly
positive there, then every exponent locally admissible for `K` at `x` is locally admissible for `K'`
at `x`: pointwise `K'^(-c) ≤ K^(-c)` near `x` (a larger base, nonpositive exponent), so `K'^(-c)` is
dominated by the locally-integrable `K^(-c)`. A larger germ integrates at least as well — its local
admissible set is at least as large. Needs `K'` measurable. -/
theorem localAdmissibleExponents_subset_of_le {K K' : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hK'meas : Measurable K') (hbound : ∀ᶠ y in 𝓝 x, 0 < K y ∧ K y ≤ K' y) :
    localAdmissibleExponents K x ⊆ localAdmissibleExponents K' x := by
  rintro c ⟨hc0, hs, hsmem, hsint⟩
  refine ⟨hc0, ?_⟩
  obtain ⟨s₀, hs₀s, hs₀open, hxs₀⟩ := mem_nhds_iff.1 hsmem
  obtain ⟨t₀, ht₀bound, ht₀open, hxt₀⟩ := eventually_nhds_iff.1 hbound
  refine ⟨s₀ ∩ t₀, (hs₀open.inter ht₀open).mem_nhds ⟨hxs₀, hxt₀⟩, ?_⟩
  have hmeas : MeasurableSet (s₀ ∩ t₀) := (hs₀open.inter ht₀open).measurableSet
  have hdom : IntegrableOn (negPow K c) (s₀ ∩ t₀) :=
    hsint.mono_set ((inter_subset_left).trans hs₀s)
  refine Integrable.mono' hdom (measurable_negPow hK'meas c).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem hmeas (fun y hy ↦ ?_)
  obtain ⟨hKypos, hKle⟩ := ht₀bound y hy.2
  rw [Real.norm_eq_abs, abs_of_nonneg (negPow_nonneg (le_of_lt (hKypos.trans_le hKle)) c)]
  simp only [negPow_apply]
  -- `(K' y)^(-c) ≤ (K y)^(-c)` : larger base, exponent `-c ≤ 0`.
  exact Real.rpow_le_rpow_of_nonpos hKypos hKle (by linarith)

end RLCT
