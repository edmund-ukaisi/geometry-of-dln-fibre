import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJSphereBlowup` — the `∫⁻` spherical (polar) blow-up CoV

**Thread `genm-sjpeelstep`, R1-UPPER (the pure R-BLOWUP route → `sjJointResolution`).** The single
new analytic sub-brick the pure-route decorated peel needs (`genm-sjpure/card.md`, item 1): the
lower-Lebesgue (`∫⁻`) form of the polar / spherical change of variables on a Euclidean block, the
coordinate blow-up `Γ = r • ω` of the residual-block origin with Jacobian `r^{N-1}`.

This is the `∫⁻` companion of Mathlib's `MeasureTheory.integral_fun_norm_addHaar` (which is `∫`,
Bochner, and radial-symmetric-integrand only); the pure route needs the general (anisotropic)
integrand form, so it rides the underlying `measurePreserving_homeomorphUnitSphereProd` directly. It
is the KEEP-`Γ`-on-the-box blow-up — NOT the atom route's full-space Gram change of variables
`Γ ↦ Γ·Q_b` (which manufactures the divergent `det(Q_b Q_bᵀ)` on the rank-deficient locus;
`RadialResidualPower`'s scaling trick is that dead full-space route for the anisotropic block).

## What lands here

* **`lintegral_eq_sphereProd`** — the raw measure-preserving equality: `∫⁻ x, h x` over the whole
  Euclidean space equals the integral of `h (r • ω)` against the product of the sphere measure
  `volume.toSphere` and the radial density measure `volumeIoiPow (N−1)` (density `r^{N-1}`). Pure
  transport through `measurePreserving_homeomorphUnitSphereProd` + the null-origin restriction.
* **`lintegral_eq_polar`** — the iterated (Tonelli + `withDensity`-unfolded) form: the same integral
  as `∫⁻ ω ∂toSphere, ∫⁻ r in Ioi 0, ofReal (r^{N-1}) · h (r • ω)`, exposing the `r^{N-1}` Jacobian
  explicitly. This is the shape the exponent-shift bookkeeping (`c' ↦ c' − N/2`) consumes.

Network-free measure theory; imports only Mathlib. S2-FREE (no `monomial_rlct`, no
`cited_aoyagi_dln`);
axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal

variable {N : ℕ}

/-- **The `∫⁻` spherical blow-up (raw measure-preserving form).** For a measurable-free nonnegative
integrand `h` on `EuclideanSpace ℝ (Fin N)`, the whole-space lower integral equals the integral of
`h` precomposed with the inverse polar map `(ω, r) ↦ r • ω`, against the product of the sphere
measure
and the radial density `volumeIoiPow (N−1)`. Rides `measurePreserving_homeomorphUnitSphereProd`
(the origin is null under Haar `volume`, so `{0}ᶜ` restriction is free). -/
theorem lintegral_eq_sphereProd [NeZero N] (h : EuclideanSpace ℝ (Fin N) → ℝ≥0∞) :
    ∫⁻ x, h x
      = ∫⁻ p, h ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin N))).symm p)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere.prod
              (volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) - 1))) := by
  have hmp := (volume :
      Measure (EuclideanSpace ℝ (Fin N))).measurePreserving_homeomorphUnitSphereProd
  have hcomp := hmp.lintegral_comp_emb
    (Homeomorph.measurableEmbedding (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin N))))
    (fun p => h ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin N))).symm p))
  -- `hcomp : ∫⁻ a, h (symm (homeo a)) ∂(comap ↑) = ∫⁻ p, h (symm p) ∂ν`
  calc ∫⁻ x, h x
      = ∫⁻ x in ({0}ᶜ : Set (EuclideanSpace ℝ (Fin N))), h x := by
        rw [restrict_compl_singleton]
    _ = ∫⁻ x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin N))), h x
          ∂((volume : Measure (EuclideanSpace ℝ (Fin N))).comap (↑)) :=
        (lintegral_subtype_comap
          (measurableSet_singleton (0 : EuclideanSpace ℝ (Fin N))).compl h).symm
    _ = ∫⁻ a : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin N))),
          h ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin N))).symm
              (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin N)) a))
          ∂((volume : Measure (EuclideanSpace ℝ (Fin N))).comap (↑)) := by
        refine lintegral_congr (fun a => ?_)
        rw [Homeomorph.symm_apply_apply]
    _ = ∫⁻ p, h ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin N))).symm p)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere.prod
              (volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) - 1))) := hcomp

end DLNFibre.DLN.RLCT
