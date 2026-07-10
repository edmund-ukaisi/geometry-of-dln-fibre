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

/-- **The radial-blow-up CoV weld on the plain product space `Fin N → ℝ`.** The transport of
`lintegral_radial_polar_factor` across the volume-preserving `ofLp : EuclideanSpace ℝ (Fin N) →
(Fin N → ℝ)` (`PiLp.volume_preserving_ofLp`), so a loss defined on the plain matrix/vector space
`Fin N → ℝ` (where `frobSq` lives) is polar-blown-up directly:

    ∫⁻ x : Fin N → ℝ, ofReal (φ (g x))
      = ∫⁻ ω ∂toSphere, ∫⁻ r in Ioi 0, ofReal (r^{N-1}) · ofReal (φ (r²·g (ofLp ω))).

The sphere `ω` lives in `EuclideanSpace ℝ (Fin N)`; `ofLp ω` is its plain-coordinate image on the
unit sphere, and `g (ofLp ω)` is the residual unit. Transport the integral, then apply the
EuclideanSpace form to `g ∘ ofLp` (still degree-2-homogeneous by `ofLp_smul`). -/
theorem lintegral_pi_radial_polar_factor {N : ℕ} [NeZero N]
    (g : (Fin N → ℝ) → ℝ) (hg : Measurable g)
    (hom : ∀ (r : ℝ) (x : Fin N → ℝ), g (r • x) = r ^ 2 * g x)
    (φ : ℝ → ℝ) (hφ : Measurable φ) :
    ∫⁻ x : Fin N → ℝ, ENNReal.ofReal (φ (g x))
      = ∫⁻ ω : sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
          ∫⁻ r in Ioi (0 : ℝ),
            ENNReal.ofReal (r ^ (N - 1))
              * ENNReal.ofReal (φ (r ^ 2 * g (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin N)))))
          ∂(volume : Measure ℝ)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) := by
  have hof : Measurable (WithLp.ofLp : EuclideanSpace ℝ (Fin N) → (Fin N → ℝ)) :=
    (PiLp.volume_preserving_ofLp (Fin N)).measurable
  have htrans : (∫⁻ x : Fin N → ℝ, ENNReal.ofReal (φ (g x)))
      = ∫⁻ y : EuclideanSpace ℝ (Fin N), ENNReal.ofReal (φ (g (WithLp.ofLp y))) :=
    ((PiLp.volume_preserving_ofLp (Fin N)).lintegral_comp
      (ENNReal.measurable_ofReal.comp (hφ.comp hg))).symm
  rw [htrans]
  have hg' : Measurable (fun y : EuclideanSpace ℝ (Fin N) => g (WithLp.ofLp y)) := hg.comp hof
  have hom' : ∀ (r : ℝ) (y : EuclideanSpace ℝ (Fin N)),
      g (WithLp.ofLp (r • y)) = r ^ 2 * g (WithLp.ofLp y) := by
    intro r y; rw [WithLp.ofLp_smul, hom]
  exact lintegral_radial_polar_factor (fun y => g (WithLp.ofLp y)) hg' hom' φ hφ

/-- **The ball-restricted radial-blow-up CoV (opaque width `N`).** The box→ball companion of
`lintegral_radial_polar_factor`: over a closed ball of radius `R ≥ 0`, the radial coordinate is
CUT OFF at `R` (the exceptional divisor ranges over `Ioc 0 R`), the direction over the unit sphere:

    ∫⁻ x in closedBall 0 R, ofReal (φ (g x))
      = ∫⁻ ω ∂toSphere, ∫⁻ r in Ioc 0 R, ofReal (r^{N-1}) · ofReal (φ (r²·g ω)).

This is the shape a matrix-box integrand lands on after `matBox ⊆ closedBall 0 √(dim)` domination:
the block radius `r = ‖x‖` is the exceptional coordinate, bounded on the box; `g ω` the residual
unit on the sphere. Apply `lintegral_eq_polar` to the ball indicator; on the sphere `‖r • ω‖ = r`
(`norm_smul`, `mem_sphere_zero_iff_norm`), so the ball membership `r • ω ∈ closedBall 0 R` collapses
to `r ∈ Ioc 0 R` (`setLIntegral_indicator`). -/
theorem lintegral_ball_radial_polar_factor {N : ℕ} [NeZero N] {R : ℝ}
    (g : EuclideanSpace ℝ (Fin N) → ℝ) (hg : Measurable g)
    (hom : ∀ (r : ℝ) (x : EuclideanSpace ℝ (Fin N)), g (r • x) = r ^ 2 * g x)
    (φ : ℝ → ℝ) (hφ : Measurable φ) :
    ∫⁻ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) R, ENNReal.ofReal (φ (g x))
      = ∫⁻ ω : sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
          ∫⁻ r in Ioc (0 : ℝ) R,
            ENNReal.ofReal (r ^ (N - 1))
              * ENNReal.ofReal (φ (r ^ 2 * g (ω : EuclideanSpace ℝ (Fin N))))
          ∂(volume : Measure ℝ)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) := by
  have hHmeas : Measurable (fun x : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (φ (g x))) :=
    ENNReal.measurable_ofReal.comp (hφ.comp hg)
  rw [← lintegral_indicator measurableSet_closedBall, lintegral_eq_polar _
    (hHmeas.indicator measurableSet_closedBall)]
  simp only [finrank_euclideanSpace_fin]
  refine lintegral_congr fun ω => ?_
  have hstep : ∀ r ∈ Ioi (0 : ℝ),
      ENNReal.ofReal (r ^ (N - 1))
          * (Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) R).indicator
              (fun x => ENNReal.ofReal (φ (g x))) (r • (ω : EuclideanSpace ℝ (Fin N)))
        = (Ioc (0 : ℝ) R).indicator
            (fun r => ENNReal.ofReal (r ^ (N - 1))
              * ENNReal.ofReal (φ (r ^ 2 * g (ω : EuclideanSpace ℝ (Fin N))))) r := by
    intro r hr
    simp only [Set.mem_Ioi] at hr
    have hnorm : ‖(r • (ω : EuclideanSpace ℝ (Fin N)))‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mem_sphere_zero_iff_norm.mp ω.2, mul_one]
    by_cases hrR : r ≤ R
    · rw [Set.indicator_of_mem (by rw [Metric.mem_closedBall, dist_zero_right, hnorm]; exact hrR),
        Set.indicator_of_mem (show r ∈ Ioc (0 : ℝ) R from ⟨hr, hrR⟩), hom r (ω : _)]
    · rw [Set.indicator_of_notMem
            (by rw [Metric.mem_closedBall, dist_zero_right, hnorm]; exact hrR),
        Set.indicator_of_notMem (show r ∉ Ioc (0 : ℝ) R from fun h => hrR h.2), mul_zero]
  rw [setLIntegral_congr_fun measurableSet_Ioi hstep, setLIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_left.mpr Set.Ioc_subset_Ioi_self]

end DLNFibre.DLN.RLCT
