/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartSweepWiring
import DLNFibre.Core.DeepChartRing
import DLNFibre.Core.SchurSideNoDrop

/-!
# `DLNFibre.Core.ChartLocalizedCoordinates` — the localizing elements of the localized chart `AlgEquiv`

Seam 1 of the route-β localized chart `AlgEquiv` (thread 31, the hard rung): pins the two localizing
elements and the rings the chart `AlgEquiv` `e : Localization.Away dsig ≃ₐ[k] Localization.Away gF`
acts between, with the `IsUnit` facts both directions consume. No descent here — denominator-free
definitions + the image-unit facts.

- `chartDsig` — the source localizing element `dsig := Quotient.mk (vanishingIdeal Σ^r) (ΔPdeep d r)`
  over `O(Σ^r)`, the class of the **deep pivot minor** (top-left `r×r` minor of the generic product).
- `chartGfib` — the schur-side localizing element `gF := map (algebraMap k O(F)) detSchurS` over
  `MvPolynomial SchurVar O(F)`, the determinant of the generic Schur Δ-block with `O(F)` coefficients
  (the exact shape `SchurSideNoDrop` / `ChartLocalizedPolyDim` consume).

The matching with the downstream wrapper `ringKrullDim_eq_of_localized_polyExtensionAlgEquiv`
(`Osig = O(Σ^r)`, `Ofib = O(F)`, `ι = SchurVar`, `dsig`, `gfib = gF`) is **definitional**.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

variable (k) in
/-- **The source localizing element** `dsig = mk (vanishingIdeal Σ^r) (ΔPdeep d r)`: the class of the
deep pivot minor (the top-left `r×r` minor of the generic product matrix) in the chart-closure
coordinate ring `O(Σ^r)`. Inverting it is the pivot chart `{detΔ ≠ 0}`. -/
noncomputable def chartDsig (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    sweepSigmaRing k d r :=
  Ideal.Quotient.mk (vanishingIdeal k (sweepSigma k d r)) (ΔPdeep d r hp hq)

variable (k) in
/-- **The schur-side localizing element** `gF = map (algebraMap k O(F)) detSchurS`: the determinant of
the generic Schur Δ-block, with `O(F)` coefficients, in `MvPolynomial SchurVar O(F)`. The exact shape
`SchurSideNoDrop.ringKrullDim_localizationAway_eq_of_schurSide` discharges (a unit `k`-coefficient
polynomial). -/
noncomputable def chartGfib (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) (sweepFibreRing k d r hp hq) :=
  MvPolynomial.map (algebraMap k (sweepFibreRing k d r hp hq))
    (detSchurS (d 0) (d (Fin.last (N + 1))) r)

/-- The image of `dsig` under the away-localization structure map is a unit (it is the inverted
element). -/
theorem isUnit_algebraMap_chartDsig (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    IsUnit (algebraMap (sweepSigmaRing k d r) (Localization.Away (chartDsig k d r hp hq))
      (chartDsig k d r hp hq)) :=
  IsLocalization.Away.algebraMap_isUnit (chartDsig k d r hp hq)

/-- The image of `gF` under the away-localization structure map is a unit (it is the inverted
element). -/
theorem isUnit_algebraMap_chartGfib (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    IsUnit (algebraMap
      (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) (sweepFibreRing k d r hp hq))
      (Localization.Away (chartGfib k d r hp hq)) (chartGfib k d r hp hq)) :=
  IsLocalization.Away.algebraMap_isUnit (chartGfib k d r hp hq)

end DLNFibre.Core
