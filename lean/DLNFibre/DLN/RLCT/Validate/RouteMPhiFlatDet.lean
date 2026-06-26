import DLNFibre.DLN.RLCT.Validate.RouteMFactorMaps
import DLNFibre.DLN.RLCT.Validate.RouteMGenFlatChart

/-!
# `RouteMPhiFlatDet` — Phase B item 4: the `phiFlat` Jacobian determinant assembly skeleton

The det-side assembly for `phiFlat_abs_det : |det Dφ_flat u| = ∏_j |u_j|^{leafH j}` (the achiever
chart Jacobian — the `cov` field of `NodeAchieverChart`). The flat achiever chart equals a `composeFold`
of the item-2 conjugated factors (radial / Schur / LDU / chain); its Jacobian determinant telescopes
(`composeFold_abs_det`, banked) to the product of the per-factor monomial dets (item 2), which sums to
`∏_j |u_j|^{leafH j}` (the `leafH3333_prod_eq` bookkeeping at opaque widths).

This module banks the ASSEMBLY: given

* the factored chart `fs : List (ChartFactor N)` with `composeFold fs = phiFlat` (**item 3**, the map
  equality — the bottleneck), and
* the per-factor det bookkeeping `(foldDerivList fs u).map |det ·| .prod = ∏_j |u_j|^{leafH j}`
  (**item 4**, from the per-factor `_abs_det`s),

the chart has fderiv `(foldDerivList fs u).prod` with `|det| = ∏_j |u_j|^{leafH j}`. The two
hypotheses crisply isolate the two open sub-pieces; the det telescope between them is closed.

* `phiFlat_hasFDerivAt_of_factored` — `phiFlat` has the factored fderiv (given the map equality).
* `phiFlat_abs_det_of_factored` — `|det Dφ_flat| = ∏_j |u_j|^{leafH j}` (given map equality + det
  bookkeeping).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (calculus + determinant; no S2).
-/

open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **`phiFlat` has the factored fderiv** `(foldDerivList fs u).prod`, given the item-3 map equality
`composeFold fs = phiFlat` (`HasFDerivAt.congr_of_eventuallyEq` from `composeFold_hasFDerivAt`). -/
theorem phiFlat_hasFDerivAt_of_factored (M t : Fin (L + 1) → ℕ) (hN : 0 < routeMAmbient M) (hL : 0 < L)
    (ht0 : t ⟨0, by omega⟩ = M 0) (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k)
    (fs : List (ChartFactor (routeMAmbient M)))
    (hmap : composeFold fs = phiFlat M t hN hL ht0 hle)
    (u : Fin (routeMAmbient M) → ℝ) :
    HasFDerivAt (phiFlat M t hN hL ht0 hle) ((foldDerivList fs u).prod) u := by
  rw [← hmap]
  exact composeFold_hasFDerivAt fs u

/-- **The `phiFlat` Jacobian determinant** `|det (fderiv φ_flat u)| = ∏_j |u_j|^{leafH j}` — the
achiever chart's `cov` Jacobian, assembled from the item-3 map equality (which pins `fderiv φ_flat u
= (foldDerivList fs u).prod`) + the item-4 per-factor det bookkeeping, via the banked telescope
`composeFold_abs_det`. This is the genuine determinant of the chart's Fréchet derivative. -/
theorem phiFlat_abs_det_of_factored (M t : Fin (L + 1) → ℕ) (hN : 0 < routeMAmbient M) (hL : 0 < L)
    (ht0 : t ⟨0, by omega⟩ = M 0) (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k)
    (fs : List (ChartFactor (routeMAmbient M)))
    (hmap : composeFold fs = phiFlat M t hN hL ht0 hle)
    (leafH : Fin (routeMAmbient M) → ℕ) (u : Fin (routeMAmbient M) → ℝ)
    (hdet : ((foldDerivList fs u).map
        (fun D : (Fin (routeMAmbient M) → ℝ) →L[ℝ] (Fin (routeMAmbient M) → ℝ) ↦
          |LinearMap.det D.toLinearMap|)).prod
      = ∏ j, |u j| ^ (leafH j)) :
    |LinearMap.det (fderiv ℝ (phiFlat M t hN hL ht0 hle) u).toLinearMap| = ∏ j, |u j| ^ (leafH j) := by
  rw [(phiFlat_hasFDerivAt_of_factored M t hN hL ht0 hle fs hmap u).fderiv,
    composeFold_abs_det fs u _ rfl, hdet]

/-! ## The map-equality-FREE det (the chart DEFINED as the factored product)

Per the item-3 design (Codex `codex/item3-form-*`): DEFINE the achiever chart AS `composeFold fs`. Then
its Jacobian determinant is `∏_j |u_j|^{leafH j}` IMMEDIATELY from the banked telescope — NO map
equality. (The map equality `composeFold fs = paramsEquivFlat ∘ chartParamsGen ∘ genBlkFlatStruct` is
needed only to TRANSFER the rate, not the determinant.) This is the genuine `phiFlat_abs_det` for the
factored chart. -/

/-- **The factored chart's Jacobian determinant** `|det (fderiv (composeFold fs) u)| =
∏_j |u_j|^{leafH j}` — immediate from `composeFold_hasFDerivAt` + the banked telescope
`composeFold_abs_det` + the item-4 per-factor det bookkeeping. NO map equality. -/
theorem composeFold_abs_det_leafH {N : ℕ} (fs : List (ChartFactor N))
    (leafH : Fin N → ℕ) (u : Fin N → ℝ)
    (hdet : ((foldDerivList fs u).map
        (fun D : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) ↦ |LinearMap.det D.toLinearMap|)).prod
      = ∏ j, |u j| ^ (leafH j)) :
    |LinearMap.det (fderiv ℝ (composeFold fs) u).toLinearMap| = ∏ j, |u j| ^ (leafH j) := by
  rw [(composeFold_hasFDerivAt fs u).fderiv, composeFold_abs_det fs u _ rfl, hdet]

end DLNFibre.DLN.RLCT
