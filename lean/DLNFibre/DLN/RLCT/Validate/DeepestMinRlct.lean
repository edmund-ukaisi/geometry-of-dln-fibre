import DLNFibre.DLN.RLCT.Skeleton
import DLNFibre.DLN.RLCT.Foundations.S1NonMPTransport

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestMinRlct` — D1 (a): the deepest core point has the min local RLCT

The D1 `≥`-leg (`rlctAt_deepest_le_of_optimal`, Skeleton): the local RLCT of the loss at the deepest
point is `≤` that at every other fibre point `v`. **VALUE-FREE** (independent of R1's resolution value)
and **NOT a citation of Aoyagi 2013 Thm 2** (the hero-task constraint: only S2 is citable). Per the
g160/#57 adjudication, the honest route (post-L2, on the homogeneous core `F = ‖∏C‖²`, `M = H−r`,
deepest = origin `0`) is NOT a one-line `rlctAt_mono` (which compares two FUNCTIONS at one point;
D1 (a) is ONE function at TWO points — the g158 gap). It decomposes into:

- **(L1-a) ray-scaling-invariance** (ELEMENTARY, value-independent): `F` homogeneous of degree `D = 2L`
  ⟹ the local RLCT is CONSTANT along the punctured ray `t ↦ t·v`, `t ∈ (0,1]`:
  `rlctAtOn F (t • v) = rlctAtOn F v`. The germ at `t·v` pulls back under the scaling diffeo `w = t·w'`
  (`rlctAtOn_comp_homeomorph`) to `t^D · (germ at v)`; the constant `t^D` is a unit
  (`rlctAtOn_unit_invariant_aux`). Reachable from green primitives + the homogeneity hypothesis.

- **(L1-b) lower-semicontinuity at the ray's limit** — LIGHT, ~10 lines from the team's OWN `rlctAt`
  def (g170/#60; the controller's `rlctAt`-def hint dissolved g160's "heavy Watanabe/Varchenko
  primitive" overestimate). `rlctAtOn F 0 ≤ rlctAtOn F v`: by `sSup_le` over admissible `c'` at `0`,
  the ray `s•v → 0` enters the open admissible `Ω` for small `s>0` (`IsOpen.mem_nhds`), so `c'` is
  admissible at `s•v` ⟹ `c' ≤ rlctAtOn (s•v) = rlctAtOn v` (L1-a). NO Fatou / Varchenko / general
  lct-semicontinuity / absent-Mathlib analysis. Value-INDEPENDENT (NOT R1's value, NOT Aoyagi Thm 2).

- **the fibre cone** (`prod (t • A) = t^L · prod A`, pure algebra): the ray `t·v` stays in the fibre and
  limits to the all-zero deepest core, so the deepest is in every stratum's closure.

STATUS: L1-a + L1-b both PROVEN (zero sorries, axiom clean-three); `deepest_le_of_homogeneous_core` (the
CORE-P1) PROVEN. The full `rlctAt_deepest_le_of_optimal` (Skeleton) wires this through L2 at every fibre
point (`deepest_regular_core_reduces` extended deepest→general-`v`) to the homogeneous core — the
remaining full-B obligation (L2-at-general-`v`), NOT this core comparison.
-/

open MeasureTheory
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

variable {N : ℕ}

/-- **(L1-a) Ray-scaling-invariance of the local RLCT** (ELEMENTARY, value-independent). For `F`
homogeneous of degree `D` (`hhomog : ∀ c w, F (c • w) = c ^ D * F w`) and `t > 0`, the local RLCT is
constant along the punctured ray: `rlctAtOn F (t • v) = rlctAtOn F v`. The scaling `σ_t : w ↦ t • w` is
a homeomorphism (`t ≠ 0`), `σ_t v = t • v`, with CONSTANT Jacobian `det (t • id) = t^N` (verified:
`ContinuousLinearMap.det` + `LinearMap.det_smul` + `det_id` + `Module.finrank_pi`).

ROUTE (two options, both elementary; the second avoids the `HasFDerivAt` instance friction):
(i) `weightedThreshold_transport` along `σ_t` (constant det `t^N`) → the `t^N` weight peeled by
`weightedThreshold_weight_unit_invariant`; then `F ∘ σ_t = t^D • F` (`hhomog`) with the `t^D` constant
peeled by `rlctAtOn_unit_invariant_aux`. (ii) DIRECT admissible-set bijection: `Ω ∋ t•v` admissible ⟺
`σ_t⁻¹ Ω ∋ v` admissible (the integral changes by the constants `t^N` (Jacobian) and `t^{-Dc'}`
(homogeneity), both finite-nonzero, so finiteness is preserved) — like `rlctAtOn_spectator_peel`'s
admissible-set argument, no `HasFDerivAt`. The reachable elementary half of D1 (a). -/
theorem rlctAtOn_ray_scaling_invariant
    (F : (Fin N → ℝ) → ℝ) (v : Fin N → ℝ) (D : ℕ) (t : ℝ) (ht0 : 0 < t)
    (hFmeas : Measurable F)
    (hhomog : ∀ (c : ℝ) (w : Fin N → ℝ), F (c • w) = c ^ D * F w) :
    rlctAtOn F (t • v) = rlctAtOn F v := by
  have htne : t ≠ 0 := ne_of_gt ht0
  -- the scaling homeomorphism `σ : w ↦ t • w`, with `σ v = t • v` and derivative `t • id` (det `t^N`).
  set σ : (Fin N → ℝ) ≃ₜ (Fin N → ℝ) := Homeomorph.smulOfNeZero t htne with hσ
  have hσapp : ∀ w, σ w = t • w := fun w => rfl
  set Dσ : (Fin N → ℝ) → ((Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) :=
    fun _ => t • ContinuousLinearMap.id ℝ (Fin N → ℝ) with hDσ
  have hderiv : ∀ x, HasFDerivAt (fun w => σ w) (Dσ x) x := fun x => by
    show HasFDerivAt (fun w => σ w) (t • ContinuousLinearMap.id ℝ (Fin N → ℝ)) x
    have : HasFDerivAt (fun w : Fin N → ℝ => t • w)
        (t • ContinuousLinearMap.id ℝ (Fin N → ℝ)) x := (hasFDerivAt_id x).const_smul t
    exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun w => (hσapp w).symm))
  have hdet : ∀ x, (Dσ x).det = t ^ N := fun x => by
    show (t • ContinuousLinearMap.id ℝ (Fin N → ℝ)).det = t ^ N
    rw [ContinuousLinearMap.det]
    simp only [ContinuousLinearMap.coe_smul, ContinuousLinearMap.coe_id, LinearMap.det_smul,
      LinearMap.det_id, mul_one, Module.finrank_pi, Module.finrank_self, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, mul_one]
  -- Step 1 (S1.1, non-MP, `E = ∅`): `wThr F 1 {t•v} = wThr (F∘σ) (|det Dσ|) {σ⁻¹(t•v)}`, basepoint `v`.
  have hpre : σ ⁻¹' {t • v} = {v} := by
    ext w; simp only [Set.mem_preimage, Set.mem_singleton_iff, hσapp]
    constructor
    · intro h; have := congrArg (fun z => t⁻¹ • z) h; simpa [smul_smul, inv_mul_cancel₀ htne] using this
    · intro h; rw [h]
  have htrans := weightedThreshold_transport F (fun _ => (1:ℝ)) (t • v) (fun w => σ w) Dσ ∅
    σ.isProperMap MeasurableSet.empty (by simp) (Set.injOn_of_injective σ.injective)
    (fun x _ => hderiv x) σ.surjective (by simp)
  rw [hpre] at htrans
  -- the transported weight is `1 · |det Dσ| = t^N` (constant, `t > 0`); rewrite `F∘σ` to the lambda.
  have hwfun : (fun w => (fun _ => (1:ℝ)) ((fun w => σ w) w) * |(Dσ w).det|)
      = fun _ : Fin N → ℝ => t ^ N := by
    funext w
    show (1 : ℝ) * |(Dσ w).det| = t ^ N
    rw [one_mul, hdet w, abs_of_pos (pow_pos ht0 N)]
  have hcompfun : (F ∘ fun w => σ w) = fun w => F (σ w) := rfl
  rw [hwfun, hcompfun] at htrans
  -- Step 2: peel the constant weight `t^N` (a bounded positive unit).
  have hpeel := weightedThreshold_weight_unit_invariant (fun w => F (σ w))
    (fun _ : Fin N → ℝ => t ^ N) v (t ^ N) (t ^ N) (pow_pos ht0 N) measurable_const
    ⟨Set.univ, Filter.univ_mem, fun _ _ => by rw [abs_of_pos (pow_pos ht0 N)]; exact ⟨le_refl _, le_refl _⟩⟩
  -- assemble: `rlctAtOn F (t•v) = wThr F 1 {t•v} = wThr (F∘σ) (t^N) {v} = wThr (F∘σ) 1 {v}`.
  rw [rlctAtOn, htrans, hpeel]
  -- Step 3: `F∘σ = t^D • F` (homogeneity); peel the constant `t^D`.
  have hFσ : (fun w => F (σ w)) = fun w => t ^ D * F w := by
    funext w; rw [hσapp, hhomog]
  rw [hFσ]
  have := rlctAtOn_unit_invariant_aux F (fun _ : Fin N → ℝ => t ^ D) v (t ^ D) (t ^ D)
    (pow_pos ht0 D) measurable_const
    ⟨Set.univ, Filter.univ_mem, fun _ _ => by rw [abs_of_pos (pow_pos ht0 D)]; exact ⟨le_refl _, le_refl _⟩⟩
  rw [rlctAtOn, weightedThreshold] at this ⊢
  exact this

/-- **(L1-b) Lower-semicontinuity of the local RLCT at the ray's origin** — LIGHT (g170/#60; the
controller's `rlctAt`-def hint dissolved g160's "heavy primitive" overestimate). The deepest core
point `0 = lim_{s→0} s • v` has RLCT `≤` the (ray-constant) RLCT at `v`: `rlctAtOn F 0 ≤ rlctAtOn F v`.
**Proof = nbhd-monotonicity of `rlctAtOn`, ~10 lines from the `sSup`/`∃Ω∋·` def:** for each admissible
`c'` at `0` (open `Ω ∋ 0`, `∫|F|^{-c'} < ⊤`), the ray `s • v → 0` enters `Ω` for small `s > 0`, so `Ω`
is a nbhd of `s • v` too ⟹ `c'` admissible at `s • v` ⟹ `c' ≤ rlctAtOn F (s•v) = rlctAtOn F v` (L1-a);
`sSup` over admissible `c'`. NO Fatou / Varchenko / absent-Mathlib analysis — value-independent. -/
theorem rlctAtOn_lsc_at_origin
    (F : (Fin N → ℝ) → ℝ) (v : Fin N → ℝ) (D : ℕ) (hFmeas : Measurable F)
    (hhomog : ∀ (c : ℝ) (w : Fin N → ℝ), F (c • w) = c ^ D * F w) :
    rlctAtOn F (0 : Fin N → ℝ) ≤ rlctAtOn F v := by
  unfold rlctAtOn weightedThreshold
  apply sSup_le
  rintro c ⟨c', rfl, Ω, hΩopen, hKΩ, hint⟩
  have h0Ω : (0 : Fin N → ℝ) ∈ Ω := hKΩ rfl
  -- the ray `s ↦ s • v` is continuous and hits `0` at `s = 0`, so it enters the open `Ω` for small `s`.
  have hcont : Continuous (fun s : ℝ => s • v) := by fun_prop
  have hpre : (fun s : ℝ => s • v) ⁻¹' Ω ∈ 𝓝 (0 : ℝ) :=
    hcont.continuousAt.preimage_mem_nhds (by
      show Ω ∈ 𝓝 ((0 : ℝ) • v)
      rw [zero_smul]; exact hΩopen.mem_nhds h0Ω)
  -- pick `s ∈ (0, 1]` with `s • v ∈ Ω` (a positive point of the nbhd of `0` in `(0,1]`).
  obtain ⟨s, hsmem, hspos, hsle⟩ :
      ∃ s : ℝ, s • v ∈ Ω ∧ 0 < s ∧ s ≤ 1 := by
    obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.1 hpre
    refine ⟨min (ε / 2) 1, ?_, by positivity, min_le_right _ _⟩
    exact hεsub (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
      calc min (ε / 2) 1 ≤ ε / 2 := min_le_left _ _
        _ < ε := by linarith)
  -- `Ω` is a nbhd of `s • v` (open), so `c'` is admissible at `s • v`; transport to `v` by L1-a.
  have hadm_sv : (c' : ℝ≥0∞) ∈ { c : ℝ≥0∞ | ∃ d : NNReal, c = (d : ℝ≥0∞) ∧
      ∃ Ω' : Set (Fin N → ℝ), IsOpen Ω' ∧ {s • v} ⊆ Ω' ∧
        IntegrableOn (fun w => |F w| ^ (-(d : ℝ)) * (fun _ => (1 : ℝ)) w) Ω' volume } :=
    ⟨c', rfl, Ω, hΩopen, Set.singleton_subset_iff.2 hsmem, hint⟩
  have hle_sv : (c' : ℝ≥0∞) ≤ rlctAtOn F (s • v) := by
    rw [rlctAtOn, weightedThreshold]; exact le_sSup hadm_sv
  rw [rlctAtOn_ray_scaling_invariant F v D s hspos hFmeas hhomog] at hle_sv
  exact hle_sv

/-- **D1 (a) core form (the homogeneity comparison).** For a homogeneous-degree-`D` core `F`, the
deepest point `0` has the minimal local RLCT over all `v`: `rlctAtOn F 0 ≤ rlctAtOn F v`. This is
exactly `rlctAtOn_lsc_at_origin` — the assembly point where L1-a (ray-constancy) + L1-b (semicontinuity
at the limit) + the cone (`0 = lim t•v` in the fibre) meet. The full `rlctAt_deepest_le_of_optimal`
(Skeleton) wires this through L2's `deepest_regular_core_reduces` (deepest and `v` both reduce to their
cores; the cores compare here). -/
theorem deepest_le_of_homogeneous_core
    (F : (Fin N → ℝ) → ℝ) (v : Fin N → ℝ) (D : ℕ) (hFmeas : Measurable F)
    (hhomog : ∀ (c : ℝ) (w : Fin N → ℝ), F (c • w) = c ^ D * F w) :
    rlctAtOn F (0 : Fin N → ℝ) ≤ rlctAtOn F v :=
  rlctAtOn_lsc_at_origin F v D hFmeas hhomog

end DLNFibre.DLN.RLCT
