import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJSigMin` — minimum stretch and singular-value submultiplicativity

**Thread `genm-vsdeep` (aoyagi-full), the (b) product-tube crux, re-expressed elementarily.** The
front-first box-bound produces a majorant `σ_r(P)^{−α}` in the *smallest singular value* `σ_r(P)` of
the product `P = A₁·A₂`; to integrate it over the factor measure the load-bearing fact is the
**singular-value submultiplicativity** `σ_r(A₁A₂) ≥ σ_r(A₁)·σ_r(A₂)`.

Rather than build the (API-poor, submultiplicativity-free) `LinearMap.singularValues`, we work with the
**minimum stretch**

    minStretch T := ⨅_{‖x‖ = 1} ‖T x‖

of a continuous linear map `T`. For a matrix `M` the smallest singular value is `minStretch (Mᵀ)`
(the smallest stretch of the *adjoint*, which is injective on the range side even when `M` is wide).
Submultiplicativity is then an elementary three-line pointwise argument — `‖T(Sx)‖ ≥ (minStretch T)·‖Sx‖
≥ (minStretch T)(minStretch S)‖x‖` — with **no** spectral theorem.

* **`minStretch T`** — `⨅_{x ∈ sphere 0 1} ‖T x‖`.
* **`minStretch_nonneg`** — `0 ≤ minStretch T`.
* **`minStretch_mul_le`** — the pointwise stretch bound `minStretch T · ‖x‖ ≤ ‖T x‖`.
* **`minStretch_comp_ge`** — submultiplicativity `minStretch T · minStretch S ≤ minStretch (T.comp S)`.

Network-free (pure normed-space analysis). Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Metric
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Minimum stretch** of a continuous linear map: the infimum of `‖T x‖` over the unit sphere. For
a matrix, the smallest singular value is the minimum stretch of its transpose/adjoint. -/
noncomputable def minStretch (T : E →L[ℝ] F) : ℝ :=
  ⨅ x : Metric.sphere (0 : E) 1, ‖T x‖

/-- The family `x ↦ ‖T x‖` over the unit sphere is bounded below (by `0`). -/
theorem bddBelow_norm_sphere (T : E →L[ℝ] F) :
    BddBelow (Set.range (fun x : Metric.sphere (0 : E) 1 => ‖T x‖)) :=
  ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩

/-- The minimum stretch is nonnegative. -/
theorem minStretch_nonneg [Nontrivial E] (T : E →L[ℝ] F) : 0 ≤ minStretch T := by
  haveI : Nonempty (Metric.sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
  exact le_ciInf (fun x => norm_nonneg _)

/-- **The pointwise stretch bound** `minStretch T · ‖x‖ ≤ ‖T x‖`, for every `x`. -/
theorem minStretch_mul_le [Nontrivial E] (T : E →L[ℝ] F) (x : E) :
    minStretch T * ‖x‖ ≤ ‖T x‖ := by
  rcases eq_or_ne x 0 with hx | hx
  · simp [hx]
  · have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    -- the normalised point on the sphere
    have hmem : (‖x‖⁻¹ • x) ∈ Metric.sphere (0 : E) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hxnorm]
    have hle : minStretch T ≤ ‖T (‖x‖⁻¹ • x)‖ :=
      ciInf_le (bddBelow_norm_sphere T) (⟨_, hmem⟩ : Metric.sphere (0 : E) 1)
    have hTs : ‖T (‖x‖⁻¹ • x)‖ = ‖x‖⁻¹ * ‖T x‖ := by
      rw [map_smul, norm_smul, norm_inv, norm_norm]
    rw [hTs] at hle
    -- multiply through by ‖x‖ > 0
    have hmul := mul_le_mul_of_nonneg_right hle (le_of_lt hxpos)
    have heq : ‖x‖⁻¹ * ‖T x‖ * ‖x‖ = ‖T x‖ := by field_simp
    rwa [heq] at hmul

/-- **Singular-value submultiplicativity** (the (b) crux): the minimum stretch of a composition is at
least the product of the minimum stretches. Applied with `T = A₂ᵀ`, `S = A₁ᵀ` this is
`σ_r(A₁A₂) ≥ σ_r(A₁)·σ_r(A₂)`. Elementary; no spectral theorem. -/
theorem minStretch_comp_ge [Nontrivial E] [Nontrivial F] (T : F →L[ℝ] G) (S : E →L[ℝ] F) :
    minStretch T * minStretch S ≤ minStretch (T.comp S) := by
  haveI : Nonempty (Metric.sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
  refine le_ciInf (fun x => ?_)
  -- `x` is on the unit sphere of `E`
  have hx : ‖(x : E)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
  calc minStretch T * minStretch S
      = minStretch T * (minStretch S * ‖(x : E)‖) := by rw [hx, mul_one]
    _ ≤ minStretch T * ‖S x‖ :=
        mul_le_mul_of_nonneg_left (minStretch_mul_le S (x : E)) (minStretch_nonneg T)
    _ ≤ ‖T (S x)‖ := minStretch_mul_le T (S x)
    _ = ‖(T.comp S) x‖ := by rw [ContinuousLinearMap.comp_apply]

/-- **Non-vacuity** — the minimum stretch of a scaling on `ℝ` is well-defined and nonnegative. -/
example (c : ℝ) : 0 ≤ minStretch (c • (1 : ℝ →L[ℝ] ℝ)) :=
  minStretch_nonneg _

end DLNFibre.DLN.RLCT
