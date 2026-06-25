/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartLocalizedCoordinates

/-!
# `DLNFibre.Core.ChartSchurConnect` — the `SchurLoc → Away gF` connecting algebra map (seam 2)

Seam 2 of the route-β localized chart `AlgEquiv` (thread 31, vehicle B): the clean coefficient
base-change `SchurLoc →ₐ[k] Localization.Away gF` that lets the LANDED `SchurLoc`-coefficient gauge
(`endpointGauge`, `gaugeEquiv_endpointGauge_multPoly`) be transported into the schur-side target ring.

The base map is `MvPolynomial.mapAlgHom (Algebra.ofId k O(F)) : MvPolynomial SchurVar k →ₐ[k]
MvPolynomial SchurVar O(F)` (push `k`-coefficients into `O(F)`); it sends `detSchurS` to exactly the
schur-side localizing element `gF = chartGfib` (definitional: `map (algebraMap k O(F)) detSchurS`).
Localizing it at `detSchurS` via `IsLocalization.Away.mapₐ` lands the algebra map
`SchurLoc = Localization.Away detSchurS →ₐ[k] Localization.Away gF`. This resolves the
"variable-gauge → SchurLoc-coefficient base-change" concern (update-5): the base-change IS clean,
`IsLocalization.Away.mapₐ` of the coefficient map.

## Main results
- `mapAlgHom_ofId_detSchurS` — `mapAlgHom (ofId k O(F)) detSchurS = chartGfib` (the unit alignment).
- `schurToGfib` — the connecting algebra map `SchurLoc →ₐ[k] Localization.Away gF`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

variable (k) in
/-- The coefficient base-change `MvPolynomial SchurVar k →ₐ[k] MvPolynomial SchurVar O(F)` sends the
schur determinant `detSchurS` to the schur-side localizing element `chartGfib` (definitionally `map
(algebraMap k O(F)) detSchurS`, and `mapAlgHom (ofId k O(F))` is `map (algebraMap k O(F))` on the
underlying ring hom). -/
theorem mapAlgHom_ofId_detSchurS (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    MvPolynomial.mapAlgHom (σ := SchurVar (d 0) (d (Fin.last (N + 1))) r)
        (Algebra.ofId k (sweepFibreRing k d r hp hq))
        (detSchurS (d 0) (d (Fin.last (N + 1))) r)
      = chartGfib k d r hp hq := by
  rw [chartGfib]
  rfl

variable (k) in
/-- **The connecting algebra map** `SchurLoc →ₐ[k] Localization.Away gF`: the localization at
`detSchurS` of the coefficient base-change `mapAlgHom (ofId k O(F))`, via `IsLocalization.Away.mapₐ`.
Carries the `SchurLoc`-coefficient gauge into the schur-side target ring. -/
noncomputable def schurToGfib (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →ₐ[k]
      Localization.Away (chartGfib k d r hp hq) :=
  haveI : IsLocalization.Away
      (MvPolynomial.mapAlgHom (σ := SchurVar (d 0) (d (Fin.last (N + 1))) r)
        (Algebra.ofId k (sweepFibreRing k d r hp hq))
        (detSchurS (d 0) (d (Fin.last (N + 1))) r))
      (Localization.Away (chartGfib k d r hp hq)) := by
    rw [mapAlgHom_ofId_detSchurS (k := k) d r hp hq]; infer_instance
  IsLocalization.Away.mapₐ (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
    (Localization.Away (chartGfib k d r hp hq))
    (MvPolynomial.mapAlgHom (Algebra.ofId k (sweepFibreRing k d r hp hq)))
    (detSchurS (d 0) (d (Fin.last (N + 1))) r)

end DLNFibre.Core
