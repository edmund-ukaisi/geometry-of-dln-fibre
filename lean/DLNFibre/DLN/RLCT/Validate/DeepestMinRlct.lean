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

/-- **(L1-b) Lower-semicontinuity of the local RLCT at the ray's origin** (the NEW heavy analytic
primitive — Watanabe/Varchenko lct-semicontinuity; value-INDEPENDENT, NOT Aoyagi Thm 2, NOT banked).
The deepest core point `0 = lim_{t→0} t • v` has RLCT `≤` the (ray-constant) RLCT at `v`:
`rlctAtOn F 0 ≤ rlctAtOn F v`. The genuine new obligation of D1 (a) (g160/#57); comparable in weight
to `weightedThreshold_transport`. NAMED sorry — surfaced, not buried. -/
theorem rlctAtOn_lsc_at_origin
    (F : (Fin N → ℝ) → ℝ) (v : Fin N → ℝ) (D : ℕ) (hD : 0 < D)
    (hFmeas : Measurable F)
    (hhomog : ∀ (c : ℝ) (w : Fin N → ℝ), F (c • w) = c ^ D * F w) :
    rlctAtOn F (0 : Fin N → ℝ) ≤ rlctAtOn F v := by
  sorry

/-- **D1 (a) core form (the homogeneity comparison).** For a homogeneous-degree-`D` core `F`, the
deepest point `0` has the minimal local RLCT over all `v`: `rlctAtOn F 0 ≤ rlctAtOn F v`. This is
exactly `rlctAtOn_lsc_at_origin` — the assembly point where L1-a (ray-constancy) + L1-b (semicontinuity
at the limit) + the cone (`0 = lim t•v` in the fibre) meet. The full `rlctAt_deepest_le_of_optimal`
(Skeleton) wires this through L2's `deepest_regular_core_reduces` (deepest and `v` both reduce to their
cores; the cores compare here). -/
theorem deepest_le_of_homogeneous_core
    (F : (Fin N → ℝ) → ℝ) (v : Fin N → ℝ) (D : ℕ) (hD : 0 < D)
    (hFmeas : Measurable F)
    (hhomog : ∀ (c : ℝ) (w : Fin N → ℝ), F (c • w) = c ^ D * F w) :
    rlctAtOn F (0 : Fin N → ℝ) ≤ rlctAtOn F v :=
  rlctAtOn_lsc_at_origin F v D hD hFmeas hhomog

end DLNFibre.DLN.RLCT
