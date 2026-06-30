import DLNFibre.DLN.RLCT.Validate.RouteMAchieverRateFields
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverWitnessInterior

/-!
# `RouteMInteriorContract` — the INTERIOR-branch achiever box-divergence contract (#3 spine)

> **SUPERSEDED-for-interior (free-K `cov` unsatisfiable; live route is `phiFlatLDU … kLDU`).** This
> contract is built on the FREE-K chart `achieverPhi = phiFlatStructV`, whose frame Jacobian carries
> `∏_s |det K_s|^{r_s+c_s}` — a degree-`t` POLYNOMIAL in the K-core coords for `t ≥ 2`, NOT a
> monomial. So `NodeAchieverChart.cov`'s pure-monomial Jacobian `∏_j |u_j|^{leafH_j}` CANNOT hold on
> this chart for the interior class, and the `hcov` hypothesis below is unsatisfiable there. The LIVE
> interior route is the LDU-lensed chart `phiFlatLDU M (tach M) ha hN (kLDU …)`, whose `kLDU` lens
> straightens each `det K_s` to the diagonal-pivot monomial `∏_i q_i` — see
> `RouteMInteriorLDUContract` (`routeMCore_box_diverges_interiorLDU`). This file is kept as the
> rate-side/`leaf_integrand` reference; do NOT mistake it for the live interior divergence route.

The spine for the INTERIOR branch of the ∀M achiever box-divergence (`hInterior` in
`RouteMAchieverDispatch`). It assembles the interior `NodeAchieverChart M` from the BANKED rate-side
fields (the achiever chart `achieverPhi`, the rate `routeMCore = (x p)²·U`, the det-FREE
det-free `leaf_integrand` for any `leafH`, and the interior `Ubound`), isolating the
OPEN chart-construction fields as precise hypotheses:

* `leafH` + `leafH_pivot` (`leafH p = minAdm M − 1`) — the multi-axis Jacobian-exponent vector;
* `Umeas` (`achieverUfun` measurable — a polynomial in the chart coords; banked-pattern);
* `cov` — the geometric change-of-variables with `|det Dφ| = ∏_j |u_j|^{leafH j}`. **THE heavy open
  piece** (the multi-block Schur-frame Jacobian; the construction-sensitive multi-axis det — the
  thread-36 det programme: LDU-coordinatize each K-core to a monomial `det K_s`, telescope via
  `composeFold_abs_det_leafH`/`schurFrame_abs_det`/`lduCoreDeriv_det`, then `injOn` off the
  weighted-axis planes + the n-fold null-slice). See `threads/80-…/interior-det-scope.md`.
* `image_subset` — the source box maps into the cube (continuity + `phi 0 = 0`; banked-pattern).

`routeMCore_box_diverges_interiorContract` discharges `BoxDiverges` GIVEN these. This banks the
interior spine (parallel to `routeMCore_box_diverges_smearedContract` for the smeared branch): the
dispatch's `hInterior` reduces to the four open fields, the rate-side + `Ubound` already closed. The
remaining content is exactly the chart `cov`/det + `leafH` + the two banked-pattern fields — NOT a
wall (every det brick is banked, `(3,3,3,3)` is the complete worked instance), a MAJOR build.

Axioms: clean-three + the cited `monomial_rlct` (inherited from the assembly's monomial atom); the
contract adds none of its own.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The INTERIOR-branch achiever box-divergence contract.** For an interior-drop `M` (`2 ≤ L`,
`1 ≤ minAdm M`), the achiever box integral diverges, GIVEN the open chart-construction fields:
the Jacobian-exponent vector `leafH` (binding `leafH p = minAdm M − 1`), measurability of the unit,
the geometric `cov` (`|det Dφ| = ∏_j |u_j|^{leafH j}`), and the image containment. The rate, the
det-free `leaf_integrand`, and the interior `Ubound` are WIRED from the banked facts
(`routeMCore_achieverPhi`, `achiever_leaf_integrand`, `achieverUbound_interior`). The pivot is the
radial `structPivot M hN = ⟨0,_⟩`. -/
theorem routeMCore_box_diverges_interiorContract (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hN : 0 < routeMAmbient M) (hInt : InteriorDrop M) (hpos : 1 ≤ minAdm M)
    (leafH : Fin (routeMAmbient M) → ℕ)
    (hleafH_pivot : leafH (structPivot M hN) = minAdm M - 1)
    (hUmeas : Measurable (achieverUfun M hL hN))
    (hcov : ∀ (V : Set (Fin (routeMAmbient M) → ℝ)), MeasurableSet V →
        ∀ (g : (Fin (routeMAmbient M) → ℝ) → ℝ≥0∞),
      ∫⁻ x in achieverPhi M hL hN '' (V \ {x | x (structPivot M hN) = 0}), g x
        = ∫⁻ u in V \ {x | x (structPivot M hN) = 0},
            ENNReal.ofReal (∏ j, |u j| ^ (leafH j)) * g (achieverPhi M hL hN u))
    (himage : ∀ ε : ℝ, 0 < ε →
        ∃ δ > 0, achieverPhi M hL hN ''
          (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ))
          ⊆ cubeBox (routeMAmbient M) ε)
    (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M) ε,
      ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤ := by
  -- assemble the interior `NodeAchieverChart M` from the banked rate-side + the open fields
  let W : NodeAchieverChart M :=
    { hpos := hpos
      phi := achieverPhi M hL hN
      p := structPivot M hN
      leafH := leafH
      leafH_pivot := hleafH_pivot
      Ufun := achieverUfun M hL hN
      Ubound := achieverUbound_interior M hL hN hInt
      Umeas := hUmeas
      leaf_integrand := fun c =>
        Filter.Eventually.of_forall (fun x => achiever_leaf_integrand M hL hN leafH c x)
      cov := hcov
      image_subset := himage }
  exact routeMCore_box_diverges_of_nodeChart M W c' hc' ε hε

end DLNFibre.DLN.RLCT
