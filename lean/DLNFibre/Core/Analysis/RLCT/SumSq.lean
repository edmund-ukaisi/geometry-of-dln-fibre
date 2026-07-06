import DLNFibre.Core.Analysis.RLCT.Local
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# `RLCT.SumSq` — the canonical sum-of-squares RLCT `rlctAt Q 0 = C/2`

The **textbook RLCT of a nondegenerate quadratic** in `C` variables, cite-free and sorry-free:
for `Q y = ∑ i, (y i)^2 = ‖y‖²_{ℓ²}` on `ℝ^C`,

`rlctAt Q 0 = C / 2`.

This is the reusable analytic **bedrock** underneath the DLN payoff: at a smooth codim-`C` point of
a fibre, the square-Frobenius loss is a nondegenerate sum of `C` squares in local coordinates, so
its local RLCT is `C/2` — the geometric content behind the cited Aoyagi `rlct = ½·codim` equality,
here established directly for the model quadratic (no cite).

## Route

`Q^(-c)(y) = ‖y‖^(-2c)` is radial. Local integrability at `0` in `ℝ^C` is governed by the
polar-coordinate / scaling threshold `∫_{ball} r^{-2c} r^{C-1} dr` converging at `0` iff
`C - 1 - 2c > -1`, i.e. `2c < C`. The load-bearing steps:

* `integrableOn_ball_norm_rpow_iff` — the reusable **ball threshold** on
  `EuclideanSpace ℝ (Fin (m+1))`: `IntegrableOn (‖·‖^s) (ball 0 R) ↔ -(m+1) < s` for `s < 0`,
  `R > 0`. Built from the global polar reduction `MeasureTheory.integrable_fun_norm_addHaar` + the
  1-D local threshold `intervalIntegral.integrableOn_Ioo_rpow_iff`, glued by the indicator bridge
  `integrable_indicator_iff` (the cutoff radial function `(Ioo 0 R).indicator (·^s)` is *pointwise*
  equal to `(ball 0 R).indicator (‖·‖^s)` once `s < 0`, via `Real.zero_rpow`).
* transported from `EuclideanSpace ℝ (Fin C)` to `Fin C → ℝ` (where `Q`/`rlctAt` live) by the
  volume-preserving equiv `PiLp.volume_preserving_toLp`.
* `mem_localAdmissibleExponents_sumSq` — the **characterization**
  `c ∈ localAdmissibleExponents Q 0 ↔ (0 ≤ c ∧ 2*c < C)`, i.e. the admissible set is
  `Set.Ico 0 (C/2)`.
* `rlctAt_sumSq` reads off `rlctAt Q 0 = sSup (Ico 0 (C/2)) = C/2` via `csSup_Ico`.

Bare Mathlib-mirror namespace `RLCT` (network-free).
-/

open MeasureTheory Set Filter Topology Real Metric

namespace RLCT

/-! ### The reusable ball threshold on Euclidean space -/

/-- **Ball integrability threshold for a negative norm power.** On `EuclideanSpace ℝ (Fin (m+1))`,
the radial function `x ↦ ‖x‖^s` (with `s < 0`, so a genuine pole at `0`) is integrable on the ball
`ball 0 R` (`R > 0`) iff `-(m+1) < s`. The dimension-`(m+1)` polar/scaling threshold, cite-free. -/
theorem integrableOn_ball_norm_rpow_iff {m : ℕ} {R : ℝ} (hR : 0 < R) {s : ℝ} (hs : s < 0) :
    IntegrableOn (fun x : EuclideanSpace ℝ (Fin (m + 1)) ↦ ‖x‖ ^ s) (ball 0 R) volume ↔
      -(m + 1 : ℝ) < s := by
  have hsne : s ≠ 0 := ne_of_lt hs
  -- The cutoff radial profile: `t^s` on `(0, R)`, `0` elsewhere.
  let g : ℝ → ℝ := fun t ↦ t ^ s
  let f : ℝ → ℝ := (Ioo (0 : ℝ) R).indicator g
  -- Step 1: `fun x ↦ f ‖x‖` is pointwise equal to `(ball 0 R).indicator (‖·‖^s)`.
  have hpt : (fun x : EuclideanSpace ℝ (Fin (m + 1)) ↦ f ‖x‖)
      = (ball (0 : EuclideanSpace ℝ (Fin (m + 1))) R).indicator (fun x ↦ ‖x‖ ^ s) := by
    funext x
    by_cases hx0 : ‖x‖ = 0
    · -- `x = 0`: LHS is `f 0 = 0`; RHS is `‖x‖^s = 0^s = 0` (in the ball since `R > 0`).
      have hxball : x ∈ ball (0 : EuclideanSpace ℝ (Fin (m + 1))) R := by
        rw [mem_ball_zero_iff, hx0]; exact hR
      simp only [f, g, hx0, Set.indicator_of_mem hxball, Real.zero_rpow hsne,
        Set.indicator_apply_eq_zero]
      intro hmem; exact absurd hmem.1 (lt_irrefl 0)
    · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx0)
      by_cases hxR : ‖x‖ < R
      · have hmem : ‖x‖ ∈ Ioo (0 : ℝ) R := ⟨hxpos, hxR⟩
        have hxball : x ∈ ball (0 : EuclideanSpace ℝ (Fin (m + 1))) R := mem_ball_zero_iff.2 hxR
        simp only [f, g, Set.indicator_of_mem hmem, Set.indicator_of_mem hxball]
      · have hmem : ‖x‖ ∉ Ioo (0 : ℝ) R := fun h ↦ hxR h.2
        have hxball : x ∉ ball (0 : EuclideanSpace ℝ (Fin (m + 1))) R :=
          fun h ↦ hxR (mem_ball_zero_iff.1 h)
        simp only [f, Set.indicator_of_notMem hmem, Set.indicator_of_notMem hxball]
  -- Step 2: ball integral ↔ integrability of the pointwise-equal radial function `f ∘ ‖·‖`.
  have h2 : IntegrableOn (fun x : EuclideanSpace ℝ (Fin (m + 1)) ↦ ‖x‖ ^ s) (ball 0 R) volume
      ↔ Integrable (fun x : EuclideanSpace ℝ (Fin (m + 1)) ↦ f ‖x‖) volume := by
    rw [hpt]; exact (integrable_indicator_iff measurableSet_ball).symm
  -- Step 3: polar reduction (global) — `f` is radial; `dim = m+1`, so `dim - 1 = m`.
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) - 1 = m := by
    rw [finrank_euclideanSpace_fin, Nat.add_sub_cancel]
  have h3 : Integrable (fun x : EuclideanSpace ℝ (Fin (m + 1)) ↦ f ‖x‖) volume
      ↔ IntegrableOn (fun t : ℝ ↦ t ^ m • f t) (Ioi 0) := by
    have := integrable_fun_norm_addHaar (F := ℝ)
      (E := EuclideanSpace ℝ (Fin (m + 1))) (volume) (f := f)
    rw [hdim] at this
    exact this
  -- Step 4: `t^m • f t = (Ioo 0 R).indicator (t^m • g t)`; reduce `Ioi 0` to `Ioo 0 R`.
  have hsmul : (fun t : ℝ ↦ t ^ m • f t)
      = (Ioo (0 : ℝ) R).indicator (fun t ↦ t ^ m • g t) := by
    funext t
    by_cases ht : t ∈ Ioo (0 : ℝ) R
    · simp only [f, Set.indicator_of_mem ht]
    · simp only [f, Set.indicator_of_notMem ht, smul_zero]
  have h4 : IntegrableOn (fun t : ℝ ↦ t ^ m • f t) (Ioi 0)
      ↔ IntegrableOn (fun t ↦ t ^ m • g t) (Ioo (0 : ℝ) R) := by
    rw [hsmul, integrableOn_indicator_iff measurableSet_Ioo,
      Set.inter_eq_self_of_subset_left Ioo_subset_Ioi_self]
  -- Step 5: on `Ioo 0 R` (where `t > 0`), `t^m • t^s = t^(m + s)`; apply the 1-D threshold.
  have h5 : IntegrableOn (fun t ↦ t ^ m • g t) (Ioo (0 : ℝ) R)
      ↔ (-(m + 1 : ℝ) < s) := by
    rw [integrableOn_congr_fun (g := fun t : ℝ ↦ t ^ ((m : ℝ) + s)) ?_ measurableSet_Ioo,
      intervalIntegral.integrableOn_Ioo_rpow_iff hR]
    · constructor
      · intro h; linarith
      · intro h; linarith
    · intro t ht
      simp only [g, smul_eq_mul]
      rw [← Real.rpow_natCast t m, ← Real.rpow_add ht.1]
  rw [h2, h3, h4, h5]

/-- **Local integrability threshold for a negative norm power at `0`.** On
`EuclideanSpace ℝ (Fin (m+1))`, `x ↦ ‖x‖^s` (`s < 0`) is integrable on *some* neighbourhood of `0`
iff `-(m+1) < s`. Reads the ball threshold off through `𝓝 0` (a nbhd of `0` both contains and is
contained-up-to-integrability by a small ball). -/
theorem integrableAtFilter_nhds_norm_rpow_iff {m : ℕ} {s : ℝ} (hs : s < 0) :
    IntegrableAtFilter (fun x : EuclideanSpace ℝ (Fin (m + 1)) ↦ ‖x‖ ^ s) (𝓝 0) volume ↔
      -(m + 1 : ℝ) < s := by
  constructor
  · rintro ⟨t, ht, hint⟩
    -- A nbhd `t` of `0` contains a ball `ball 0 R`; integrability descends to it.
    obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.1 ht
    exact (integrableOn_ball_norm_rpow_iff hR hs).1 (hint.mono_set hsub)
  · intro h
    -- The ball `ball 0 1` is a witnessing neighbourhood.
    exact ⟨ball 0 1, ball_mem_nhds 0 one_pos, (integrableOn_ball_norm_rpow_iff one_pos hs).2 h⟩

/-! ### The sum-of-squares kernel -/

variable {C : ℕ}

/-- The nondegenerate quadratic kernel `Q y = ∑ i, (y i)^2` on `ℝ^C` (the squared ℓ²-norm). -/
noncomputable def sumSq (C : ℕ) : (Fin C → ℝ) → ℝ := fun y ↦ ∑ i, (y i) ^ 2

@[simp] lemma sumSq_apply (y : Fin C → ℝ) : sumSq C y = ∑ i, (y i) ^ 2 := rfl

/-- `sumSq` is nonnegative (a sum of squares). -/
lemma sumSq_nonneg (y : Fin C → ℝ) : 0 ≤ sumSq C y := by
  simp only [sumSq]; positivity

/-- On `EuclideanSpace ℝ (Fin C)`, `sumSq` composed with `WithLp.ofLp` is the squared ℓ²-norm. -/
lemma sumSq_ofLp (x : EuclideanSpace ℝ (Fin C)) : sumSq C (WithLp.ofLp x) = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [sumSq]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [Real.norm_eq_abs, sq_abs]

/-- **Characterization of the locally-admissible exponents of the sum-of-squares kernel at `0`.**
For `C ≥ 1`, `c` is locally admissible for `Q = ∑ (·)^2` at `0` iff `0 ≤ c` and `2c < C`;
equivalently, the admissible set is `Set.Ico 0 (C/2)`. Cite-free; the `name = content` `iff`.
(The `C ≥ 1` hypothesis is load-bearing: at `C = 0`, `Q ≡ 0` and every `c ≥ 0` is admissible, so
the admissible set is not `Ico 0 0 = ∅`.) -/
theorem mem_localAdmissibleExponents_sumSq (hC : 1 ≤ C) {c : ℝ} :
    c ∈ localAdmissibleExponents (sumSq C) 0 ↔ (0 ≤ c ∧ 2 * c < C) := by
  obtain ⟨m, rfl⟩ : ∃ m, C = m + 1 := ⟨C - 1, by omega⟩
  rw [mem_localAdmissibleExponents]
  -- It remains, given `0 ≤ c`, to compute the local integrability of `(∑ (·)^2)^(-c)` at `0`.
  refine and_congr_right (fun hc0 ↦ ?_)
  -- Transport from `Fin (m+1) → ℝ` (where `sumSq`/`rlctAt` live) to `EuclideanSpace ℝ (Fin (m+1))`
  -- via the volume-preserving homeomorphism `ofLp`, which sends `𝓝 0 ↦ 𝓝 0` and `volume ↦ volume`.
  set e : EuclideanSpace ℝ (Fin (m + 1)) → (Fin (m + 1) → ℝ) := WithLp.ofLp with he
  have hemb : MeasurableEmbedding e :=
    (MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)).symm.measurableEmbedding
  have hmapμ : (volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).map e = volume :=
    (PiLp.volume_preserving_ofLp (Fin (m + 1))).map_eq
  have hmapl : Filter.map e (𝓝 (0 : EuclideanSpace ℝ (Fin (m + 1)))) = 𝓝 (0 : Fin (m + 1) → ℝ) := by
    have h := ((WithLp.linearEquiv 2 ℝ (Fin (m + 1) → ℝ)).toContinuousLinearEquiv.toHomeomorph
      ).map_nhds_eq 0
    simpa [he] using h
  -- The composite `negPow (sumSq (m+1)) c ∘ e` is `x ↦ ‖x‖^(-(2c))`.
  have hcomp : (negPow (sumSq (m + 1)) c) ∘ e = fun x ↦ ‖x‖ ^ (-(2 * c)) := by
    funext x
    simp only [Function.comp_apply, negPow_apply, he, sumSq_ofLp x]
    rw [← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_mul (norm_nonneg x)]
    ring_nf
  have htransport : IntegrableAtFilter (negPow (sumSq (m + 1)) c) (𝓝 0) volume ↔
      IntegrableAtFilter
        (fun x : EuclideanSpace ℝ (Fin (m + 1)) ↦ ‖x‖ ^ (-(2 * c))) (𝓝 0) volume := by
    rw [← hcomp, ← hemb.integrableAtFilter_map_iff, hmapl, hmapμ]
  rw [htransport]
  -- Now on Euclidean space: `s := -(2c)`. Split `c = 0` (constant, integrable) vs `c > 0` (pole).
  rcases eq_or_lt_of_le hc0 with hc | hc
  · -- `c = 0`: the germ is the constant `1`; integrable near `0`, and `2·0 < m+1` holds.
    subst hc
    constructor
    · intro _
      have : (0 : ℝ) < ((m : ℝ) + 1) := by positivity
      simpa using this
    · intro _
      refine ⟨ball 0 1, ball_mem_nhds 0 one_pos, ?_⟩
      have : (fun x : EuclideanSpace ℝ (Fin (m + 1)) ↦ ‖x‖ ^ (-(2 * (0 : ℝ))))
          = fun _ ↦ (1 : ℝ) := by
        funext x; norm_num
      rw [this]; exact integrableOn_const
  · -- `c > 0`: `s = -(2c) < 0`; apply the local threshold.
    have hs : -(2 * c) < 0 := by linarith
    rw [integrableAtFilter_nhds_norm_rpow_iff hs]
    constructor
    · intro h; push_cast at h ⊢; linarith
    · intro h; push_cast at h ⊢; linarith

/-- **The sum-of-squares RLCT.** For `C ≥ 1`, the local RLCT of the nondegenerate quadratic
`Q = ∑ i, (y i)^2` at `0` is `C/2`. Cite-free, sorry-free — the model-quadratic bedrock under the
DLN `rlct = ½·codim` payoff. -/
theorem rlctAt_sumSq (hC : 1 ≤ C) : rlctAt (sumSq C) 0 = (C : ℝ) / 2 := by
  have hCpos : (0 : ℝ) < (C : ℝ) / 2 := by
    have : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
    linarith
  have hset : localAdmissibleExponents (sumSq C) 0 = Set.Ico 0 ((C : ℝ) / 2) := by
    ext c
    rw [mem_localAdmissibleExponents_sumSq hC, Set.mem_Ico]
    constructor
    · rintro ⟨hc0, hc⟩; exact ⟨hc0, by linarith⟩
    · rintro ⟨hc0, hc⟩; exact ⟨hc0, by linarith⟩
  rw [rlctAt_def, hset, csSup_Ico hCpos]

end RLCT
