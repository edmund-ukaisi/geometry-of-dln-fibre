import DLNFibre.DLN.RLCT.Validate.RouteMStairHeadline
import DLNFibre.DLN.RLCT.Validate.RouteMChainAssembleDiff

/-!
# `RouteMInteriorDetReal` — the interior-det headline on the REAL chart `phiFlatLiveR1` (route-2)

The interior-det headline `interiorDet_headline_of_stairConj` (route-2 staircase) tied to the ACTUAL flat
chart `phiFlatLiveR1` — NOT an engine surrogate. The Jacobian is `fderiv ℝ (phiFlatLiveR1 …) u`, whose
EXISTENCE is the banked `phiFlatLiveR1_differentiableAt`; this module records that IF that real Jacobian
is conjugate to a route-2 staircase (the layer-collecting `LinearEquiv e` + the engine diagonal blocks),
the real chart's Jacobian abs-det IS the headline monomial.

This makes the residual PRECISE and SOUND: the lone remaining obligation is the staircase conjugacy
`fderiv ℝ phiFlatLiveR1 u = e.symm ∘ stairMap V (L+1) f c ∘ e` with the engine block-det identifications —
the faithful expression of the REAL `fderiv` as a staircase over the opaque chart-coordinate widths (the
cast-heavy multi-tide construction the `staircase-det-bricks-statement-card.md` flags). It is stated on
`fderiv ℝ (phiFlatLiveR1 …)` so it CANNOT be discharged by an engine surrogate (Codex's flagged trap).

* `interiorDet_phiFlatLiveR1_of_stairConj` — the REAL-chart headline, given the staircase conjugacy of
  `fderiv ℝ phiFlatLiveR1` + the engine identifications. Output formula identical to
  `interiorDet_headline_of_blockTri`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (the abstract headline + the linear-map det; no new
analysis — the real `fderiv` enters only as the conjugated object).
-/

open scoped BigOperators

noncomputable section

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The interior-det HEADLINE on the REAL chart `phiFlatLiveR1`.** Let `D := fderiv ℝ (phiFlatLiveR1 …)
u` be the actual Jacobian (its existence is `phiFlatLiveR1_differentiableAt`). If `D` (as a `LinearMap`)
is conjugate — through a layer-collecting `LinearEquiv e : (Fin (routeMAmbient M) → ℝ) ≃ₗ StairProd V
(L+1)` — to the route-2 staircase `stairMap V (L+1) f c`, with the radial layer-`0` block-det
`|det (f 0)| = |u_p|^{minAdm−1}` and each boundary layer-`s+1` block-det equal to the Schur⊗LDU engine
value, then the real chart's Jacobian abs-det factorizes:

  `|det (fderiv phiFlatLiveR1 u)| = |u_p|^{minAdm−1} · ∏_s ( |det K_s|^{r_s+c_s} · ∏_i |q_{s,i}|^{…} )`.

This is the SOUND route-2 headline on the genuine chart: the hypothesis is a property of the REAL
`fderiv`, so it is not dischargeable by a surrogate. The remaining work is to BUILD the conjugacy `hconj`
(the faithful staircase decomposition of `fderiv phiFlatLiveR1` over the opaque chart-coordinate widths).
-/
theorem interiorDet_phiFlatLiveR1_of_stairConj
    (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)]
    [∀ k, FiniteDimensional ℝ (V k)]
    (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (hN : 0 < routeMAmbient M) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (u : Fin (routeMAmbient M) → ℝ)
    (f : (s : ℕ) → V s →ₗ[ℝ] V s) (c : StairCoupling V (L + 1))
    (e : (Fin (routeMAmbient M) → ℝ) ≃ₗ[ℝ] StairProd V (L + 1))
    (hconj : (fderiv ℝ (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin) u).toLinearMap
        = (e.symm : StairProd V (L + 1) →ₗ[ℝ] (Fin (routeMAmbient M) → ℝ))
          ∘ₗ stairMap V (L + 1) f c
          ∘ₗ (e : (Fin (routeMAmbient M) → ℝ) →ₗ[ℝ] StairProd V (L + 1)))
    (up : ℝ) (tK : Fin L → ℕ) (rc : Fin L → ℕ) (Kdet : Fin L → ℝ)
    (q : (s : Fin L) → Fin (tK s) → ℝ)
    (hR : |LinearMap.det (f 0)| = |up| ^ (minAdm M - 1))
    (hB : ∀ s : Fin L, |LinearMap.det (f (s.val + 1))|
      = |Kdet s| ^ (rc s) * ∏ i : Fin (tK s), |q s i| ^ (2 * ((tK s : ℕ) - 1 - (i : ℕ)))) :
    |LinearMap.det (fderiv ℝ (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin) u).toLinearMap|
      = |up| ^ (minAdm M - 1)
        * ∏ s : Fin L,
            (|Kdet s| ^ (rc s) * ∏ i : Fin (tK s), |q s i| ^ (2 * ((tK s : ℕ) - 1 - (i : ℕ)))) :=
  interiorDet_headline_of_stairConj V M f c e
    (fderiv ℝ (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin) u).toLinearMap hconj
    up tK rc Kdet q hR hB

end DLNFibre.DLN.RLCT

end
