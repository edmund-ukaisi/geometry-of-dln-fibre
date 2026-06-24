/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.DeterminantalBasePresentation

/-!
# `DLNFibre.Core.SchurGauge` — the Schur-valued pivot block as a `SchurLoc`-unit (route-(c) rung 2)

The first easier piece of the route-(c) pivot-chart trivialization (thread 31 rung 2): the pivot
block `schurΔ` (the top-left `r×r` submatrix of the generic base matrix, in the `SchurVar`
coordinates), mapped into the localization `SchurLoc = Localization.Away detSchurS`, is an
**invertible matrix**. Its determinant is `detSchurS`, the very element inverted in `SchurLoc`. It
is the unit out of which the endpoint normalizing gauge `L`, `H` (Schur-complement blocks) is built
— the `BaseChangeGroup` element over `SchurLoc` that drives the chart `AlgEquiv`.

This module stays strictly at the `varietyDim`/radical level (the `VarietyDimRadical` shield); it
never re-enters the strict-ideal / reducedness level that walled R2-3b-4.

## Main results
- `schurΔLoc` — the pivot block over `SchurLoc`.
- `det_schurΔLoc` — its determinant is `detSchurS` pushed into `SchurLoc`.
- `isUnit_det_schurΔLoc` — that determinant is a unit (inverted in `SchurLoc`).
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {k : Type u} [Field k]

/-- The pivot block `schurΔ` mapped into the localization
`SchurLoc = Localization.Away detSchurS`. -/
noncomputable def schurΔLoc (q p r : ℕ) :
    Matrix (Fin r) (Fin r) (SchurLoc (k := k) q p r) :=
  (schurΔ (k := k) q p r).map (algebraMap _ _)

/-- The determinant of `schurΔLoc` is `detSchurS`, pushed into `SchurLoc`. (`detSchurS` is by
definition `det schurΔ`, and `det` commutes with the algebra map.) -/
theorem det_schurΔLoc (q p r : ℕ) :
    (schurΔLoc (k := k) q p r).det
      = algebraMap (MvPolynomial (SchurVar q p r) k) (SchurLoc (k := k) q p r)
          (detSchurS (k := k) q p r) :=
  (RingHom.map_det (algebraMap (MvPolynomial (SchurVar q p r) k) (SchurLoc (k := k) q p r))
    (schurΔ (k := k) q p r)).symm

/-- **The pivot block is invertible over `SchurLoc`.** Its determinant `detSchurS` is the element
inverted in `SchurLoc = Localization.Away detSchurS`, hence a unit. -/
theorem isUnit_det_schurΔLoc (q p r : ℕ) : IsUnit (schurΔLoc (k := k) q p r).det := by
  rw [det_schurΔLoc]
  exact IsLocalization.Away.algebraMap_isUnit (detSchurS q p r)

end DLNFibre.Core

/-- Non-vacuity witness: at `(q,p,r) = (2,2,1)` over `ℚ`, the `1×1` pivot block over `SchurLoc` is
invertible (the existential is inhabited). -/
example : IsUnit (DLNFibre.Core.schurΔLoc (k := ℚ) 2 2 1).det :=
  DLNFibre.Core.isUnit_det_schurΔLoc 2 2 1
