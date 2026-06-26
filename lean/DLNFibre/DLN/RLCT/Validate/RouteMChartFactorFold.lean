import DLNFibre.DLN.RLCT.Validate.RouteMAchieverGeneralDet
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.LinearAlgebra.Determinant

/-!
# `RouteMChartFactorFold` — the abstract `ChartFactor` prefix-fold scaffold (Phase B3, reusable spine)

The reusable, network-free scaffold for the achiever-chart Jacobian determinant: a `List` of full-ambient
chart factors (each a `(Fin N → ℝ) → (Fin N → ℝ)` carrying its `HasFDerivAt` and its absolute determinant
AT A GIVEN POINT), composed by `foldr (· ∘ ·)`, with:

* `composeFold` — the composite map `f₀ ∘ f₁ ∘ ⋯ ∘ f_{n−1}`.
* `composeFold_hasFDerivAt` — the composite has fderiv `(D f₀ at prefix₀) ∘L ⋯ ∘L (D f_{n−1} at u)`,
  the chain rule folded over the list (the prefix-evaluation: factor `i`'s derivative at the output of the
  factors to its right — the `Frame3333Deriv (Kparam3333 u)` pattern).
* `composeFold_abs_det` — `|det D(composite) u| = ∏ |det (D fᵢ at its prefix)|`, the telescope via
  `general_composed_clm_abs_det` (banked) over the prefix-evaluated per-factor derivative CLMs.

This is the prefix-aware composition spine. The per-`M` achiever chart instantiates it with the concrete
factors (radial / Schur / LDU / chain, each conjugated to a full-ambient CLM); each factor's `absDet` is the
banked Phase-A value (`schurFrame_abs_det`, `lduCoreDeriv_det`, `chainUnit_det`, `pivotBlowupOn_abs_det`).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (calculus + determinant; no S2).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

variable {N : ℕ}

/-- **A chart factor**: a full-ambient self-map `f` of `Fin N → ℝ` carrying, at every point, its fderiv
`D` (a CLM) with `HasFDerivAt`. (The absolute determinant is read off `D` per-point at the use-site; this
structure is the differentiable-factor datum the prefix-fold composes.) -/
structure ChartFactor (N : ℕ) where
  /-- The factor map. -/
  f : (Fin N → ℝ) → (Fin N → ℝ)
  /-- The factor's fderiv at each point. -/
  D : (Fin N → ℝ) → ((Fin N → ℝ) →L[ℝ] (Fin N → ℝ))
  /-- `f` has fderiv `D u` at every `u`. -/
  hasD : ∀ u, HasFDerivAt f (D u) u

/-- The composite map `f₀ ∘ f₁ ∘ ⋯ ∘ f_{n−1}` of a list of chart factors (`foldr (· ∘ ·) id`). -/
def composeFold (fs : List (ChartFactor N)) : (Fin N → ℝ) → (Fin N → ℝ) :=
  fs.foldr (fun F g => F.f ∘ g) id

@[simp] theorem composeFold_nil : composeFold ([] : List (ChartFactor N)) = id := rfl

@[simp] theorem composeFold_cons (F : ChartFactor N) (fs : List (ChartFactor N)) :
    composeFold (F :: fs) = F.f ∘ composeFold fs := rfl

/-- The prefix-evaluated derivative CLM list of a factor list at a point `u`: factor `i`'s derivative
`D` evaluated at the output `composeFold (tail) u` of the factors to its right (the prefix). -/
def foldDerivList (fs : List (ChartFactor N)) (u : Fin N → ℝ) :
    List ((Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) :=
  match fs with
  | [] => []
  | F :: rest => F.D (composeFold rest u) :: foldDerivList rest u

@[simp] theorem foldDerivList_nil (u : Fin N → ℝ) :
    foldDerivList ([] : List (ChartFactor N)) u = [] := rfl

@[simp] theorem foldDerivList_cons (F : ChartFactor N) (fs : List (ChartFactor N)) (u : Fin N → ℝ) :
    foldDerivList (F :: fs) u = F.D (composeFold fs u) :: foldDerivList fs u := rfl

/-- **The composite has fderiv `(foldDerivList fs u).prod`** at `u` — the chain rule folded over the
list, with each factor's derivative evaluated at its prefix output. -/
theorem composeFold_hasFDerivAt (fs : List (ChartFactor N)) (u : Fin N → ℝ) :
    HasFDerivAt (composeFold fs) ((foldDerivList fs u).prod) u := by
  induction fs with
  | nil =>
      rw [composeFold_nil, foldDerivList_nil, List.prod_nil]
      exact hasFDerivAt_id (𝕜 := ℝ) u
  | cons F rest ih =>
      rw [composeFold_cons, foldDerivList_cons, List.prod_cons]
      -- `(F.f ∘ composeFold rest)` has fderiv `(F.D (composeFold rest u)) ∘L (foldDerivList rest u).prod`.
      exact (F.hasD (composeFold rest u)).comp u ih

/-- **The composite Jacobian determinant telescopes** (abs form): `|det D(composeFold fs) u| =
∏ |det (D fᵢ at prefixᵢ)|` — the prefix-evaluated per-factor abs-dets, via the banked
`general_composed_clm_abs_det`. The reusable prefix-fold det spine. -/
theorem composeFold_abs_det (fs : List (ChartFactor N)) (u : Fin N → ℝ) (m : List ℝ)
    (hfac : (foldDerivList fs u).map
      (fun D : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) ↦ |LinearMap.det D.toLinearMap|) = m) :
    |LinearMap.det ((foldDerivList fs u).prod).toLinearMap| = m.prod :=
  general_composed_clm_abs_det N (foldDerivList fs u) m hfac

/-! ## Non-vacuity: a two-factor fold telescopes -/

/-- A two-factor fold's composite has fderiv `D F (G.f u) ∘L D G u`, det telescoping to
`|det (D F (G.f u))| · |det (D G u)|`. Confirms the prefix-evaluation + the telescope fire. -/
example (F G : ChartFactor N) (u : Fin N → ℝ) :
    |LinearMap.det (((foldDerivList [F, G] u).prod).toLinearMap)|
      = |LinearMap.det (F.D (G.f u)).toLinearMap|
        * (|LinearMap.det (G.D u).toLinearMap| * 1) := by
  rw [composeFold_abs_det [F, G] u
    [|LinearMap.det (F.D (G.f u)).toLinearMap|, |LinearMap.det (G.D u).toLinearMap|] (by
    simp only [foldDerivList_cons, foldDerivList_nil, composeFold_cons, composeFold_nil,
      List.map_cons, List.map_nil]
    rfl)]
  simp [List.prod_cons, List.prod_nil]

end DLNFibre.DLN.RLCT
