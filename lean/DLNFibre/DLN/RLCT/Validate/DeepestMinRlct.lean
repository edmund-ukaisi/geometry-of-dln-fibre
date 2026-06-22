import DLNFibre.DLN.RLCT.Skeleton

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

- **(L1-b) lower-semicontinuity at the ray's limit** (the NEW heavy analytic primitive): the deepest
  `0 = lim_{t→0} t·v`, and `rlctAtOn F 0 ≤ liminf_{t→0} rlctAtOn F (t•v)`. Value-INDEPENDENT (the most
  singular point of a family has the min RLCT — Watanabe/Varchenko lct-semicontinuity, NOT the
  resolution, NOT Aoyagi Thm 2), but a genuinely NEW primitive (comparable to `weightedThreshold_transport`),
  NOT banked in the harness/Mathlib. Carried as a NAMED `sorry` + surfaced (g160/#57).

- **the fibre cone** (`prod (t • A) = t^L · prod A`, pure algebra): the ray `t·v` stays in the fibre and
  limits to the all-zero deepest core, so the deepest is in every stratum's closure.

ROUTE-FIRST: L1-a stated with the homogeneity as a hypothesis (fm3's `dlnLoss_homogeneous_layer`
discharges it on `dlnLoss M 0`); L1-b the named heavy primitive; the assembly composes them. The full
`rlctAt_deepest_le_of_optimal` wires through L2 (`deepest_regular_core_reduces`) to the core.
-/

open MeasureTheory
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

variable {N : ℕ}

/-- **(L1-a) Ray-scaling-invariance of the local RLCT** (ELEMENTARY, value-independent). For `F`
homogeneous of degree `D` (`hhomog : ∀ t w, F (t • w) = t ^ D * F w`) and `t ∈ (0,1]`, the local RLCT
is constant along the punctured ray: `rlctAtOn F (t • v) = rlctAtOn F v`. The scaling `w = t • w'` is a
homeomorphism (`t ≠ 0`); the germ pulls back to `t^D · (germ at v)`, the `t^D` a positive unit. -/
theorem rlctAtOn_ray_scaling_invariant
    (F : (Fin N → ℝ) → ℝ) (v : Fin N → ℝ) (D : ℕ) (t : ℝ) (ht0 : 0 < t)
    (hhomog : ∀ (c : ℝ) (w : Fin N → ℝ), F (c • w) = c ^ D * F w) :
    rlctAtOn F (t • v) = rlctAtOn F v := by
  sorry

/-- **(L1-b) Lower-semicontinuity of the local RLCT at the ray's origin** — LIGHT (g170/#60; the
controller's `rlctAt`-def hint dissolved g160's "heavy primitive" overestimate). The deepest core
point `0 = lim_{s→0} s • v` has RLCT `≤` the (ray-constant) RLCT at `v`: `rlctAtOn F 0 ≤ rlctAtOn F v`.
**Proof = nbhd-monotonicity of `rlctAtOn`, ~10 lines from the `sSup`/`∃Ω∋·` def:** for each admissible
`c'` at `0` (open `Ω ∋ 0`, `∫|F|^{-c'} < ⊤`), the ray `s • v → 0` enters `Ω` for small `s > 0`, so `Ω`
is a nbhd of `s • v` too ⟹ `c'` admissible at `s • v` ⟹ `c' ≤ rlctAtOn F (s•v) = rlctAtOn F v` (L1-a);
`sSup` over admissible `c'`. NO Fatou / Varchenko / absent-Mathlib analysis — value-independent. -/
theorem rlctAtOn_lsc_at_origin
    (F : (Fin N → ℝ) → ℝ) (v : Fin N → ℝ) (D : ℕ)
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
  rw [rlctAtOn_ray_scaling_invariant F v D s hspos hhomog] at hle_sv
  exact hle_sv

/-- **D1 (a) core form (the homogeneity comparison).** For a homogeneous-degree-`D` core `F`, the
deepest point `0` has the minimal local RLCT over all `v`: `rlctAtOn F 0 ≤ rlctAtOn F v`. This is
exactly `rlctAtOn_lsc_at_origin` — the assembly point where L1-a (ray-constancy) + L1-b (semicontinuity
at the limit) + the cone (`0 = lim t•v` in the fibre) meet. The full `rlctAt_deepest_le_of_optimal`
(Skeleton) wires this through L2's `deepest_regular_core_reduces` (deepest and `v` both reduce to their
cores; the cores compare here). -/
theorem deepest_le_of_homogeneous_core
    (F : (Fin N → ℝ) → ℝ) (v : Fin N → ℝ) (D : ℕ)
    (hhomog : ∀ (c : ℝ) (w : Fin N → ℝ), F (c • w) = c ^ D * F w) :
    rlctAtOn F (0 : Fin N → ℝ) ≤ rlctAtOn F v :=
  rlctAtOn_lsc_at_origin F v D hhomog

end DLNFibre.DLN.RLCT
