import DLNFibre.DLN.RLCT.Validate.RouteMCardBridge
import DLNFibre.DLN.RLCT.Validate.RouteMFlatLive
import DLNFibre.DLN.RLCT.Validate.RouteMPhiTargetDet

/-!
# `RouteMInteriorDet` — the interior chart's monomial Jacobian det (2b-i-C/D, map-equality as hypothesis)

The det-side assembly for the interior `NodeAchieverChart`'s `cov` field: `|det Dφ(u)| =
∏_j |u_j|^{leafH j}`, with the binding `leafH (structPivot) = minAdm M − 1`. The chart is
`phiFlatLiveR1 ∘ kLDU` (the R1 active-center live-leaf decoder ∘ the LDU lens; both banked sorry-free).

Per the spec's build order (cast-light isolated from cast-heavy), this module takes the **item-3 map
equality** `composeFold fs = phi` as a HYPOTHESIS (mirroring the banked
`RouteMPhiTargetDet.phiTarget_abs_det_of_factored` / `RouteMPhiFlatDet.phiFlat_abs_det_of_factored`) — the
opaque-width map equality (2b-i-B) is the genuine cast weight and is spec-gated separately. Given the map
equality + the per-factor det bookkeeping, the det is the banked `composeFold`-telescope (CAST-LIGHT, no
`chartIdxEquiv` surgery), and the pivot exponent is `minAdm − 1` via `RouteMCardBridge.radialLeafH_pivot`.

* `interiorDet_of_factored` — `|det Dφ| = ∏_j |u_j|^{leafH j}` for the interior chart `phi`, given the map
  equality + det bookkeeping (the `cov`-det input).
* `interiorLeafH_pivot` — the `leafH (structPivot) = minAdm − 1` binding (the `NodeAchieverChart.leafH_pivot`
  field), for the radial-pivot exponent vector with `active.card = minAdm`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (calculus + determinant + the banked minAdm; no S2).
-/

open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The interior chart's monomial Jacobian det, given the factored map equality + det bookkeeping.**
For any interior chart `phi` (e.g. `phiFlatLiveR1 ∘ kLDU`) with a factorization `composeFold fs = phi`
and the per-factor abs-det product equal to `∏_j |u_j|^{leafH j}`, the Jacobian determinant is that
monomial. The `cov`-det input; a thin specialization of `phiTarget_abs_det_of_factored` (the cast-light
`composeFold` telescope). The map equality `hmap` is the item-3 obligation (2b-i-B, spec-gated). -/
theorem interiorDet_of_factored {N : ℕ} (phi : (Fin N → ℝ) → (Fin N → ℝ))
    (fs : List (ChartFactor N)) (hmap : composeFold fs = phi)
    (leafH : Fin N → ℕ) (u : Fin N → ℝ)
    (hdet : ((foldDerivList fs u).map
        (fun D : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) ↦ |LinearMap.det D.toLinearMap|)).prod
      = ∏ j, |u j| ^ (leafH j)) :
    |LinearMap.det (fderiv ℝ phi u).toLinearMap| = ∏ j, |u j| ^ (leafH j) :=
  phiTarget_abs_det_of_factored phi fs hmap leafH u hdet

/-- **The interior `leafH_pivot` binding** `leafH (structPivot) = minAdm M − 1` for the radial-pivot
exponent vector `leafH j := if j = structPivot then active.card − 1 else 0` at the achiever active set
(`active.card = minAdm M`). Discharges `NodeAchieverChart.leafH_pivot` / the contract's `hleafH_pivot`. -/
theorem interiorLeafH_pivot (M : Fin (L + 1) → ℕ) (hN : 0 < routeMAmbient M)
    (active : Finset (Fin (routeMAmbient M))) (hcard : active.card = minAdm M) :
    (fun j => if j = structPivot M hN then active.card - 1 else 0) (structPivot M hN)
      = minAdm M - 1 :=
  radialLeafH_pivot M hN active hcard

/-- **Non-vacuity**: the interior-det assembly fires on a concrete 2-factor fold (a linear reshape ∘ the
radial blow-up at the achiever active set), giving `|det Dφ| = |u_p|^{minAdm−1}` (the pure-radial interior
shape — the per-boundary Schur/LDU factors add the spectator monomials). Confirms the wiring. -/
example {N : ℕ} (active : Finset (Fin N)) (p : Fin N) (hp : p ∈ active)
    (Q : ChartFactor N) (hQdet : ∀ u, |LinearMap.det (Q.D u).toLinearMap| = 1)
    (phi : (Fin N → ℝ) → (Fin N → ℝ))
    (hmap : composeFold [Q, radialFactor active p] = phi) (u : Fin N → ℝ) :
    |LinearMap.det (fderiv ℝ phi u).toLinearMap|
      = ∏ j, |u j| ^ ((fun j => if j = p then active.card - 1 else 0) j) := by
  refine interiorDet_of_factored phi [Q, radialFactor active p] hmap _ u ?_
  simp only [foldDerivList_cons, foldDerivList_nil, composeFold_cons, composeFold_nil, id_eq,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [hQdet, radialFactor_abs_det active p hp, one_mul]
  rw [Finset.prod_eq_single p]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ _) h

end DLNFibre.DLN.RLCT
