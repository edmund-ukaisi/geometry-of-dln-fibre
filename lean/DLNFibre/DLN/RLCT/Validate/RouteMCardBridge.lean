import DLNFibre.DLN.RLCT.Validate.RouteMBudget
import DLNFibre.DLN.RLCT.Validate.RouteMRadialFactor
import DLNFibre.DLN.RLCT.Validate.NodeAchieverChart
import DLNFibre.DLN.RLCT.Validate.RouteMFlatStructV

/-!
# `RouteMCardBridge` — the card-bridge `active.card = minAdm` + the −1 lemma (2b-i-A, cast-light)

The count-level core of the interior chart's radial degree: the radial blow-up `pivotBlowupOn active p`
of the achiever center has `active.card = minAdm M` active directions, so its Jacobian radial exponent is
`active.card − 1 = minAdm M − 1` (`radialFactor_abs_det`). This discharges the `leafH (structPivot) =
minAdm − 1` field (`NodeAchieverChart.leafH_pivot`) once `leafH` is the factored-det exponent vector.

**Cast-light** (the (a)/budget discipline): the count is pure ℕ arithmetic — `minAdm` (banked) + the
existence of a `minAdm`-card subset of `Fin N` containing the pivot (`Finset.exists_superset_card_eq`),
given `minAdm M ≤ routeMAmbient M` (codim ≤ ambient dimension). NO `chartIdxEquiv`-level Fin-N bijection
in the count — `active`'s *identity* (which slots) is the item-3 map-equality's concern (2b-i-B), not the
count's.

* `radialActive_exists` — `∃ active, structPivot ∈ active ∧ active.card = minAdm` (given `minAdm ≤ N`,
  `1 ≤ minAdm`); the achiever radial active set.
* `radialLeafH_pivot` — the −1 lemma in its abstract form: for the radial exponent vector
  `leafH p := active.card − 1` (`0` elsewhere) with `active.card = minAdm`, `leafH (structPivot) =
  minAdm − 1`. The `NodeAchieverChart.leafH_pivot` discharge (the radial axis carries `minAdm − 1`;
  spectator LDU/Schur axes are `k = 0`, threshold-neutral — `nodeChart_thresholdLe`).
* `radial_abs_det_minAdm` — the radial factor's det at the achiever active set is `|u_p|^{minAdm−1}`.

Honest naming (genm-budgetrev): `budget_identity` is TOTAL budget = minAdm; the −1 is `active.card − 1`
(the one fixed pivot — the gauge). This file proves `active.card − 1 = minAdm − 1`, NOT
`#angular = minAdm − 1` as a `budget_identity` restatement.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (finite cardinality + the banked minAdm).
-/

open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The achiever radial active set (existence + cardinality) -/

/-- **The achiever radial active set exists**: given `1 ≤ minAdm M ≤ routeMAmbient M`, there is a
`Finset (Fin (routeMAmbient M))` of cardinality `minAdm M` containing the radial pivot `structPivot`.
The blow-up active set of the codim-`minAdm` achiever center. (`Finset.exists_superset_card_eq` from the
singleton `{p}`: `1 ≤ minAdm` gives `{p}.card = 1 ≤ minAdm`, `minAdm ≤ N` gives room in `univ`.) -/
theorem radialActive_exists (M : Fin (L + 1) → ℕ) (hN : 0 < routeMAmbient M)
    (hpos : 1 ≤ minAdm M) (hle : minAdm M ≤ routeMAmbient M) :
    ∃ active : Finset (Fin (routeMAmbient M)),
      structPivot M hN ∈ active ∧ active.card = minAdm M := by
  obtain ⟨active, hsub, hcard⟩ := Finset.exists_superset_card_eq
    (show ({structPivot M hN} : Finset (Fin (routeMAmbient M))).card ≤ minAdm M by
      rw [Finset.card_singleton]; exact hpos)
    (show minAdm M ≤ (Finset.univ : Finset (Fin (routeMAmbient M))).card by
      rw [Finset.card_univ, Fintype.card_fin]; exact hle)
  exact ⟨active, hsub (Finset.mem_singleton_self _), hcard⟩

/-! ## The radial determinant at the achiever active set + the −1 lemma -/

/-- **The radial blow-up det at the achiever active set is `|u_p|^{minAdm−1}`** — `radialFactor_abs_det`
at `active.card = minAdm` (`p ∈ active`). The radial contribution to the chart's monomial Jacobian. -/
theorem radial_abs_det_minAdm (M : Fin (L + 1) → ℕ) (hN : 0 < routeMAmbient M)
    (active : Finset (Fin (routeMAmbient M))) (hp : structPivot M hN ∈ active)
    (hcard : active.card = minAdm M) (u : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det ((radialFactor active (structPivot M hN)).D u).toLinearMap|
      = |u (structPivot M hN)| ^ (minAdm M - 1) := by
  rw [radialFactor_abs_det active (structPivot M hN) hp u, hcard]

/-- **The −1 lemma (abstract radial form)**: the radial exponent vector
`leafH j := if j = structPivot then active.card − 1 else 0`, at `active.card = minAdm M`, has
`leafH (structPivot) = minAdm M − 1` — the `NodeAchieverChart.leafH_pivot` field. (The spectator
LDU/Schur axes — `0` here — are filled by the per-boundary factors in 2b-i-C/D; they carry `k = 0` in
the loss-base, threshold-neutral via `nodeChart_thresholdLe`.) -/
theorem radialLeafH_pivot (M : Fin (L + 1) → ℕ) (hN : 0 < routeMAmbient M)
    (active : Finset (Fin (routeMAmbient M))) (hcard : active.card = minAdm M) :
    (fun j => if j = structPivot M hN then active.card - 1 else 0) (structPivot M hN)
      = minAdm M - 1 := by
  simp only [↓reduceIte, hcard]

end DLNFibre.DLN.RLCT
