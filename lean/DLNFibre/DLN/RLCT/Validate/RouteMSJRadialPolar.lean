import DLNFibre.DLN.RLCT.Validate.RouteMSJSphereBlowup
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

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

/-! ## The corner-block finiteness (the L3/L4 landing) -/

/-- **The 1-D radial power integral is finite below the pole.** `∫⁻ r in Ioc 0 R, ofReal (r^e) < ⊤`
for every `e > -1` and any `R` — the singularity at `r = 0` is integrable exactly when `e > -1`
(`R ≤ 0` gives the empty domain). Bridges Mathlib's `intervalIntegrable_rpow'` (`-1 < e`) through
`IntegrableOn.setLIntegral_lt_top`. This is the exceptional-divisor radial integral the corner
resolution lands on: `e = (N-1) - 2c'` (Jacobian power `N-1`, loss order `2`), finite iff
`c' < N/2`. -/
theorem lintegral_Ioc_rpow_lt_top {R e : ℝ} (he : -1 < e) :
    ∫⁻ r in Ioc (0 : ℝ) R, ENNReal.ofReal (r ^ e) < ⊤ := by
  by_cases hR : R ≤ 0
  · rw [Set.Ioc_eq_empty (not_lt.mpr hR)]; simp
  · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt (not_le.mp hR))).mp
      (intervalIntegral.intervalIntegrable_rpow' he)).setLIntegral_lt_top

/-- **The corner-block finiteness (opaque width `N`, the L3/L4 landing).** For a measurable
degree-2-homogeneous loss `g : EuclideanSpace ℝ (Fin N) → ℝ` (`g (r • x) = r²·g x`) whose value on
the unit sphere is bounded below by `a > 0` (the vslice cert §8 unit-boundedness, carried as
hypothesis), and any exponent `c' < N/2`, the box (here: any closed ball, the `matBox ⊆ closedBall`
shape) integral of the loss power is finite:

    ∫⁻ z in closedBall 0 R, ofReal ((g z) ^ (-c')) < ⊤.

**The corner sum is a special case.** The vslice §5 corner model `gX(Γ) + gY(v)` (two blocks of
dims `h₀+1`, `h₁+1` sharing the deep factor) is itself a single degree-2-homogeneous loss on the
JOINT block `(Γ, v)` of dimension `N = (h₀+1) + (h₁+1) = h₀+h₁+2`, with `a ≤ (gX+gY)` on the joint
sphere (from `a ≤ gX`, `a ≤ gY` on the respective spheres). So `c' < N/2 = (h₀+h₁+2)/2` reproduces
the branch threshold where "the codimensions ADD" — the SUM threshold, not the min undershoot.

Proof (the resolution compass, no det-inverse): the ball radial blow-up
(`lintegral_ball_radial_polar_factor`) exposes the monomial Jacobian `r^{N-1}` and factors the loss
`(r²·g ω)^{-c'}`; on the sphere `g ω ≥ a > 0`, so `(r²·g ω)^{-c'} ≤ a^{-c'}·r^{-2c'}` (rpow
antitone), dominating the integrand by the separated monomial `a^{-c'}·r^{(N-1)-2c'}`; the radial
integral is
finite (`lintegral_Ioc_rpow_lt_top`, `(N-1)-2c' > -1 ⟺ c' < N/2`) and the sphere measure is finite
(`IsFiniteMeasure`). -/
theorem corner_block_lintegral_lt_top {N : ℕ} [NeZero N] {R : ℝ}
    (g : EuclideanSpace ℝ (Fin N) → ℝ) (hg : Measurable g)
    (hom : ∀ (r : ℝ) (x : EuclideanSpace ℝ (Fin N)), g (r • x) = r ^ 2 * g x)
    (c' : ℝ) (hc0 : 0 ≤ c') (hc' : c' < (N : ℝ) / 2) (a : ℝ) (ha : 0 < a)
    (hlb : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin N)) 1, a ≤ g (ω : EuclideanSpace ℝ (Fin N))) :
    ∫⁻ z in Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) R,
        ENNReal.ofReal ((g z) ^ (-c')) < ⊤ := by
  have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub hNpos, Nat.cast_one]
  set p : ℝ := ((N : ℝ) - 1) - 2 * c' with hp_def
  have hp : -1 < p := by rw [hp_def]; linarith [hc']
  have hφmeas : Measurable (fun t : ℝ => t ^ (-c')) := by fun_prop
  rw [lintegral_ball_radial_polar_factor g hg hom (fun t => t ^ (-c')) hφmeas]
  -- inner bound: for each sphere direction, dominate by the separated monomial
  have key : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
      (∫⁻ r in Ioc (0 : ℝ) R,
          ENNReal.ofReal (r ^ (N - 1))
            * ENNReal.ofReal ((r ^ 2 * g (ω : EuclideanSpace ℝ (Fin N))) ^ (-c')))
        ≤ ENNReal.ofReal (a ^ (-c')) * ∫⁻ r in Ioc (0 : ℝ) R, ENNReal.ofReal (r ^ p) := by
    intro ω
    rw [← lintegral_const_mul' (ENNReal.ofReal (a ^ (-c'))) _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioc (fun r hr => ?_)
    have hr0 : 0 < r := hr.1
    have hgω : a ≤ g (ω : EuclideanSpace ℝ (Fin N)) := hlb ω
    -- the real-value domination `r^{N-1}·(r²·gω)^{-c'} ≤ a^{-c'}·r^p`
    have hr2a : 0 < r ^ 2 * a := by positivity
    have hr2ge : r ^ 2 * a ≤ r ^ 2 * g (ω : EuclideanSpace ℝ (Fin N)) :=
      mul_le_mul_of_nonneg_left hgω (by positivity)
    have hanti : (r ^ 2 * g (ω : EuclideanSpace ℝ (Fin N))) ^ (-c') ≤ (r ^ 2 * a) ^ (-c') :=
      Real.rpow_le_rpow_of_nonpos hr2a hr2ge (neg_nonpos.mpr hc0)
    have hsplit : (r ^ 2 * a) ^ (-c') = (r ^ 2 : ℝ) ^ (-c') * a ^ (-c') :=
      Real.mul_rpow (by positivity) ha.le
    have hpow : r ^ (N - 1) * (r ^ 2 : ℝ) ^ (-c') = r ^ p := by
      rw [show (r : ℝ) ^ (N - 1) = r ^ (((N - 1 : ℕ) : ℝ)) from (Real.rpow_natCast r (N - 1)).symm,
        show (r ^ 2 : ℝ) = r ^ ((2 : ℕ) : ℝ) from (Real.rpow_natCast r 2).symm,
        ← Real.rpow_mul hr0.le, ← Real.rpow_add hr0]
      congr 1
      rw [hcast, hp_def]; push_cast; ring
    have hreal : r ^ (N - 1) * (r ^ 2 * g (ω : EuclideanSpace ℝ (Fin N))) ^ (-c')
        ≤ a ^ (-c') * r ^ p := by
      calc r ^ (N - 1) * (r ^ 2 * g (ω : EuclideanSpace ℝ (Fin N))) ^ (-c')
          ≤ r ^ (N - 1) * (r ^ 2 * a) ^ (-c') :=
            mul_le_mul_of_nonneg_left hanti (by positivity)
        _ = r ^ (N - 1) * ((r ^ 2 : ℝ) ^ (-c') * a ^ (-c')) := by rw [hsplit]
        _ = a ^ (-c') * (r ^ (N - 1) * (r ^ 2 : ℝ) ^ (-c')) := by ring
        _ = a ^ (-c') * r ^ p := by rw [hpow]
    calc ENNReal.ofReal (r ^ (N - 1))
            * ENNReal.ofReal ((r ^ 2 * g (ω : EuclideanSpace ℝ (Fin N))) ^ (-c'))
        = ENNReal.ofReal (r ^ (N - 1) * (r ^ 2 * g (ω : EuclideanSpace ℝ (Fin N))) ^ (-c')) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (a ^ (-c') * r ^ p) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (a ^ (-c')) * ENNReal.ofReal (r ^ p) :=
          ENNReal.ofReal_mul (by positivity)
  refine lt_of_le_of_lt (lintegral_mono key) ?_
  rw [lintegral_const]
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_Ioc_rpow_lt_top hp))
    (measure_lt_top _ _)

/-- **The corner-block finiteness over the cube box (matrix coordinates, the direct
`gammaPeelIntegral` shape).** For a measurable degree-2-homogeneous loss `g : (Fin n → ℝ) → ℝ` (the
flattened matrix block, where `frobSq` lives) with `a ≤ g (ofLp ω) > 0` on the unit sphere and
`c' < n/2`, the integral over
the cube box `[-1,1]^n` (the `matBox` shape) of the loss power is finite:

    ∫⁻ z in [-1,1]^n, ofReal ((g z) ^ (-c')) < ⊤.

The matrix-coordinate landing consumed by the `(S,J)` peel: transport the cube integral to
`EuclideanSpace` along the volume-preserving `ofLp` (`setLIntegral_comp_preimage`), note the cube
image sits in `closedBall 0 √n` (`EuclideanSpace.norm_eq`, `∑ (y i)² ≤ n` on the cube), and apply
the Euclidean-coordinate `corner_block_lintegral_lt_top` to `g ∘ ofLp`. -/
theorem corner_block_cube_lintegral_lt_top {n : ℕ} [NeZero n]
    (g : (Fin n → ℝ) → ℝ) (hg : Measurable g)
    (hom : ∀ (r : ℝ) (x : Fin n → ℝ), g (r • x) = r ^ 2 * g x)
    (c' : ℝ) (hc0 : 0 ≤ c') (hc' : c' < (n : ℝ) / 2) (a : ℝ) (ha : 0 < a)
    (hlb : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        a ≤ g (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin n)))) :
    ∫⁻ z in Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1),
        ENNReal.ofReal ((g z) ^ (-c')) < ⊤ := by
  have hof : Measurable (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) :=
    (PiLp.volume_preserving_ofLp (Fin n)).measurable
  have hom' : ∀ (r : ℝ) (y : EuclideanSpace ℝ (Fin n)),
      g (WithLp.ofLp (r • y)) = r ^ 2 * g (WithLp.ofLp y) :=
    fun r y => by rw [WithLp.ofLp_smul, hom]
  have hfmeas : Measurable (fun z : Fin n → ℝ => ENNReal.ofReal ((g z) ^ (-c'))) :=
    ENNReal.measurable_ofReal.comp ((by fun_prop : Measurable fun t : ℝ => t ^ (-c')).comp hg)
  have hcube_meas : MeasurableSet (Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1)) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  -- the preimage cube sits inside `closedBall 0 √n`
  have hsub : (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) ⁻¹'
        (Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1))
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt n) := by
    intro y hy
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] at hy
    rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    calc ∑ i, ‖(y : EuclideanSpace ℝ (Fin n)) i‖ ^ 2
        ≤ ∑ _i : Fin n, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have hb : |(y : EuclideanSpace ℝ (Fin n)) i| ≤ 1 := abs_le.mpr ⟨(hy i).1, (hy i).2⟩
          rw [Real.norm_eq_abs]
          nlinarith [abs_nonneg ((y : EuclideanSpace ℝ (Fin n)) i), hb]
      _ = (n : ℝ) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; simp
  -- transport the cube integral to `EuclideanSpace` along `ofLp`, dominate by the ball, apply core
  calc ∫⁻ z in Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1),
          ENNReal.ofReal ((g z) ^ (-c'))
      = ∫⁻ y in (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) ⁻¹'
            (Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1)),
          ENNReal.ofReal ((g (WithLp.ofLp y)) ^ (-c')) :=
        ((PiLp.volume_preserving_ofLp (Fin n)).setLIntegral_comp_preimage hcube_meas hfmeas).symm
    _ ≤ ∫⁻ y in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt n),
          ENNReal.ofReal ((g (WithLp.ofLp y)) ^ (-c')) := lintegral_mono_set hsub
    _ < ⊤ := corner_block_lintegral_lt_top (fun y => g (WithLp.ofLp y)) (hg.comp hof)
        hom' c' hc0 hc' a ha hlb

/-- **Non-vacuity witness.** The pure squared-norm loss `g z = ∑ᵢ (z i)²` (the `frobSq` of the
flattened block) is degree-2-homogeneous, measurable, and equals `1` on the unit sphere, so the
hypotheses of `corner_block_cube_lintegral_lt_top` are jointly satisfiable (at `a = 1`) — the corner
finiteness is not vacuously true. -/
example {n : ℕ} [NeZero n] (c' : ℝ) (hc0 : 0 ≤ c') (hc' : c' < (n : ℝ) / 2) :
    ∫⁻ z in Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1),
        ENNReal.ofReal ((∑ i, (z i) ^ 2) ^ (-c')) < ⊤ := by
  refine corner_block_cube_lintegral_lt_top (fun z => ∑ i, (z i) ^ 2) (by fun_prop)
    (fun r z => by simp only [Pi.smul_apply, smul_eq_mul, mul_pow]; rw [Finset.mul_sum]) c' hc0 hc'
    1 one_pos (fun ω => ?_)
  have hnorm : ‖(ω : EuclideanSpace ℝ (Fin n))‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
  have hsq : (∑ i, ‖(ω : EuclideanSpace ℝ (Fin n)) i‖ ^ 2) = 1 := by
    have h2 := EuclideanSpace.norm_eq (ω : EuclideanSpace ℝ (Fin n))
    rw [hnorm] at h2
    nlinarith [Real.sq_sqrt (by positivity :
      (0 : ℝ) ≤ ∑ i, ‖(ω : EuclideanSpace ℝ (Fin n)) i‖ ^ 2), h2.symm]
  have hcongr : (∑ i, (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin n)) i) ^ 2)
      = ∑ i, ‖(ω : EuclideanSpace ℝ (Fin n)) i‖ ^ 2 :=
    Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])
  exact le_of_eq (hcongr.trans hsq).symm

end DLNFibre.DLN.RLCT
