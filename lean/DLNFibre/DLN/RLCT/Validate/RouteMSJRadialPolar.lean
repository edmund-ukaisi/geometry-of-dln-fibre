import DLNFibre.DLN.RLCT.Validate.RouteMSJSphereBlowup

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJRadialPolar` — the radial-blow-up CoV weld (opaque width)

**Thread `genm-covprod`, Stage 2 (S,J) native resolution, the L3/L4 radial CoV atom.** The reusable
change-of-variables step that BOTH radial blow-ups of the corner construction instantiate
(vslice cert §4b `Γ = u₀·Γ̂` and §4c `v = u₁·v̄`): the polar (spherical) blow-up of a Euclidean
block, exposing the radial Jacobian `r^{N-1}` and factoring a **degree-2-homogeneous** loss
`g (r • ω) = r²·g ω` out along the radius.

## What lands here

* **`lintegral_radial_polar_factor`** — for any measurable degree-2-homogeneous loss
  `g : EuclideanSpace ℝ (Fin N) → ℝ` and any measurable post-composition `φ`, the whole-space lower
  integral of `φ ∘ g` equals the iterated sphere-then-radial integral with the Jacobian `r^{N-1}`
  exposed and the loss factored `g (r • ω) = r²·g ω`:

      ∫⁻ x, ofReal (φ (g x))
        = ∫⁻ ω ∂toSphere, ∫⁻ r in Ioi 0, ofReal (r^{N-1}) · ofReal (φ (r²·g ω)).

  This is `RouteMSJSphereBlowup.lintegral_eq_polar` specialised to the loss integrand, with
  `finrank ℝ (EuclideanSpace ℝ (Fin N)) = N` (`finrank_euclideanSpace_fin`) and the homogeneity
  `g (r • ω) = r²·g ω` collapsing the inner point-value. The radial coordinate `r = ‖x‖` is the
  exceptional divisor; `g ω` is the residual **unit** on the sphere (the `Uᵢ` of the corner
  endpoint).

Network-free measure theory built on the banked polar CoV; S2-FREE (no `monomial_rlct`, no
`cited_aoyagi_dln`); axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Metric
open scoped ENNReal

/-- **The radial-blow-up CoV weld (opaque width `N`).** For a measurable degree-2-homogeneous loss
`g : EuclideanSpace ℝ (Fin N) → ℝ` (`g (r • x) = r²·g x`) and any measurable `φ : ℝ → ℝ`, the
whole-space lower integral of `ofReal (φ (g x))` equals the iterated sphere-then-radial integral
with the radial Jacobian `r^{N-1}` exposed and the loss factored along the radius:

    ∫⁻ x, ofReal (φ (g x))
      = ∫⁻ ω ∂toSphere, ∫⁻ r in Ioi 0, ofReal (r^{N-1}) · ofReal (φ (r²·g ω)).

`lintegral_eq_polar` at `h x := ofReal (φ (g x))` (measurable), with the finrank collapsed to `N`
and the point value `h (r • ω) = ofReal (φ (r²·g ω))` from homogeneity. -/
theorem lintegral_radial_polar_factor {N : ℕ} [NeZero N]
    (g : EuclideanSpace ℝ (Fin N) → ℝ) (hg : Measurable g)
    (hom : ∀ (r : ℝ) (x : EuclideanSpace ℝ (Fin N)), g (r • x) = r ^ 2 * g x)
    (φ : ℝ → ℝ) (hφ : Measurable φ) :
    ∫⁻ x, ENNReal.ofReal (φ (g x))
      = ∫⁻ ω : sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
          ∫⁻ r in Ioi (0 : ℝ),
            ENNReal.ofReal (r ^ (N - 1))
              * ENNReal.ofReal (φ (r ^ 2 * g (ω : EuclideanSpace ℝ (Fin N))))
          ∂(volume : Measure ℝ)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) := by
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (φ (g x))) :=
    ENNReal.measurable_ofReal.comp (hφ.comp hg)
  rw [lintegral_eq_polar _ hmeas]
  simp only [finrank_euclideanSpace_fin, hom]

end DLNFibre.DLN.RLCT
