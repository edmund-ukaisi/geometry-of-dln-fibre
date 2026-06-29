import DLNFibre.DLN.RLCT.Validate.RouteMRadialFactor
import DLNFibre.DLN.RLCT.Validate.RouteMCardBridge
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# `RouteMRadialComp` — route-#1 wiring: `det (D(B ∘ radial)) = |u_p|^{minAdm−1}·|det DB|`

The least-cast faithful assembly (genm-detradj 2nd-eye verdict, `codex/G-faithfulness-answer.md` +
`pnp-radial-adjudication`): the chart factors as `φ = B ∘ pivotBlowupOn active p` (MAP-level),
so by the chain rule `Dφ = DB ∘L pivotBlowupOnDeriv` and `det Dφ = det DB · det Prad` by
`LinearMap.det_comp`, with `det Prad = u_p^{minAdm−1}` (banked `pivotBlowupOnDeriv_det`). NO global
coordinate equiv (`stairConj`'s `e.symm ∘ stairMap ∘ e` is strictly heavier), NO scaled-columns `G`,
no matrix inverse / `u_p = 0` split (`det_comp` needs no invertibility).

This module banks the route-#1 WIRING (abstract in `B`/`DB`/`active`): given the map factorization,
the radial fderiv, and the u-free boundary det `|det DB| = ∏_s engine s`, the chart's Jacobian
abs-det IS the headline monomial. The three remaining obligations are then PRECISE:
(1) the MAP identity `φ = B ∘ pivotBlowupOn active p` (per-block, opaque widths — ∀M obligation);
(2) `HasFDerivAt B DB` (B polynomial, no global e);
(3) `|det DB| = ∏_s engine s` (B carries no u, so each boundary block IS the engine value —
    `schurFrame_abs_det` × `lduCoreDeriv_abs_det`).

* `radialComp_abs_det` — the wiring: `|det (fderiv ℝ (B ∘ pivotBlowupOn active p) u)| =
  |u_p|^{minAdm−1} · |det DB|`, from the map factorization + `HasFDerivAt B DB` + the radial card.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (calculus + determinant; no analysis beyond
the chain rule + the banked radial fderiv).
-/

open scoped BigOperators

noncomputable section

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The route-#1 radial-composition wiring.** Let `φ = B ∘ pivotBlowupOn active p` (`hφ`), with
`B` having fderiv `DB` at `pivotBlowupOn active p u` (`hB`), the pivot `p ∈ active`
(`hp`), and the radial active set of size `minAdm` (`hcard`). Then the chart's Jacobian abs-det is
`|u_p|^{minAdm−1} · |det DB|`. Chain rule (`HasFDerivAt.comp` + the banked radial `HasFDerivAt`) +
`LinearMap.det_comp` + the banked `radial_abs_det_minAdm`. -/
theorem radialComp_abs_det (M : Fin (L + 1) → ℕ) (hN : 0 < routeMAmbient M)
    (active : Finset (Fin (routeMAmbient M))) (hp : structPivot M hN ∈ active)
    (hcard : active.card = minAdm M)
    (B : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ))
    (φ : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ))
    (u : Fin (routeMAmbient M) → ℝ)
    (DB : (Fin (routeMAmbient M) → ℝ) →L[ℝ] (Fin (routeMAmbient M) → ℝ))
    (hφ : φ = B ∘ pivotBlowupOn active (structPivot M hN))
    (hB : HasFDerivAt B DB (pivotBlowupOn active (structPivot M hN) u)) :
    |LinearMap.det (fderiv ℝ φ u).toLinearMap|
      = |u (structPivot M hN)| ^ (minAdm M - 1) * |LinearMap.det DB.toLinearMap| := by
  -- the radial factor has the banked `HasFDerivAt` at `u`
  have hrad : HasFDerivAt (pivotBlowupOn active (structPivot M hN))
      (pivotBlowupOnDeriv active (structPivot M hN) u) u :=
    hasFDerivWithinAt_univ.mp
      (pivotBlowupOn_hasFDerivWithinAt active (structPivot M hN) Set.univ u)
  -- the composite `φ = B ∘ radial` has fderiv `DB ∘L Prad`
  have hcomp : HasFDerivAt φ (DB.comp (pivotBlowupOnDeriv active (structPivot M hN) u)) u := by
    rw [hφ]; exact hB.comp u hrad
  rw [hcomp.fderiv]
  -- `det (DB ∘L Prad) = det DB · det Prad`; `|det Prad| = |u_p|^{minAdm−1}`
  rw [ContinuousLinearMap.coe_comp, LinearMap.det_comp, abs_mul, mul_comm]
  congr 1
  exact radial_abs_det_minAdm M hN active hp hcard u

/-! ## Non-vacuity: the wiring fires on a concrete factorization

On the identity boundary `B = id`, `φ = pivotBlowupOn active p`, the wiring gives `|det Dφ| =
|u_p|^{minAdm−1} · 1` — the radial-only chart. Confirms the route-#1 conditional is satisfiable. -/

/-- **Non-vacuity (`B = id`).** With `B = id` (`DB = id`, `|det| = 1`), the chart is the radial
blow-up itself and the wiring gives `|det Dφ| = |u_p|^{minAdm−1} · 1`. -/
example (M : Fin (L + 1) → ℕ) (hN : 0 < routeMAmbient M)
    (active : Finset (Fin (routeMAmbient M))) (hp : structPivot M hN ∈ active)
    (hcard : active.card = minAdm M) (u : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det (fderiv ℝ (pivotBlowupOn active (structPivot M hN)) u).toLinearMap|
      = |u (structPivot M hN)| ^ (minAdm M - 1)
        * |LinearMap.det (ContinuousLinearMap.id ℝ (Fin (routeMAmbient M) → ℝ)).toLinearMap| := by
  refine radialComp_abs_det M hN active hp hcard id _ u (ContinuousLinearMap.id ℝ _) ?_ ?_
  · funext x; rfl
  · exact (ContinuousLinearMap.id ℝ _).hasFDerivAt

end DLNFibre.DLN.RLCT

end
