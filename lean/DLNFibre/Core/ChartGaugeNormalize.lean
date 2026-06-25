/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.EndpointNormalization
import DLNFibre.Core.SchurGauge

/-!
# `DLNFibre.Core.ChartGaugeNormalize` — the gauge-conjugation transport over `SchurLoc` (step-3a)

The first brick of the route-(c) step-3 AlgEquiv descent (thread 31): the **unconditional**
gauge-conjugation transport of the generic product, instantiated at the endpoint Schur gauge over
`SchurLoc`. From the LANDED `EndpointNormalization.gaugeEquiv_multPoly` (which gives the conjugated
product `P_last · multPoly · P_0⁻¹` for any gauge `P`), specialised to `P = endpointGauge` (`L⁻¹` at
the target vertex, `H` at the source vertex):

> `gaugeEquiv (endpointGauge) (multPoly r c) = ((Lmat)⁻¹ · multPoly · (Hmat)⁻¹) r c`   (over `SchurLoc`).

This is pure algebra — no locus condition — and is the bridge that, modulo the chart-locus vanishing
ideal (where the Schur relation forces the normalized product to `diag(I_r,0)`), gives the
gauge-normalization (3b). Stays strictly over the localized coefficient ring `SchurLoc`; the
`vanishingIdeal` descent is (3b)+ downstream.

## Main results
- `gaugeEquiv_endpointGauge_multPoly` — the conjugation transport at `endpointGauge`, over `SchurLoc`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {k : Type u} [Field k]

/-- The lifted endpoint gauge `liftGauge (endpointGauge)` at the target vertex `last N` is the
`C`-image of `Lmat⁻¹` (the unit pushed into `MvPolynomial (RepCoord d) SchurLoc`). For `N ≥ 1`
(`Fin (N+2)`), via `endpointGauge_last` and the definition of `liftGauge`. -/
theorem liftGauge_endpointGauge_last {N : ℕ} (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    Units.val (liftGauge d (endpointGauge (k := k) d r hp hq) (Fin.last (N + 1)))
      = ((Units.val (isUnit_Lmat (k := k) (d 0) (d (Fin.last (N + 1))) r hp).unit⁻¹).map
          (C : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →+*
            MvPolynomial (RepCoord d) (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r))) := by
  rw [liftGauge, endpointGauge_last]
  rfl

/-- The inverse of the lifted endpoint gauge at the source vertex `0` is the `C`-image of `Hmat⁻¹`. -/
theorem liftGauge_endpointGauge_zero_inv {N : ℕ} (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    Units.val ((liftGauge d (endpointGauge (k := k) d r hp hq) 0)⁻¹)
      = ((Units.val (isUnit_Hmat (k := k) (d 0) (d (Fin.last (N + 1))) r hq).unit⁻¹).map
          (C : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →+*
            MvPolynomial (RepCoord d) (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r))) := by
  rw [liftGauge, endpointGauge_zero, Units.coe_map_inv]
  rfl

/-- **The gauge-conjugation transport at the endpoint gauge (over `SchurLoc`).** Instantiating the
LANDED `gaugeEquiv_multPoly` at `P = endpointGauge`: the gauge `AlgEquiv` sends the generic product
entry `multPoly r c` to the `(r, c)` entry of `L⁻¹ · (Matrix.of multPoly) · H⁻¹`, where `L`, `H` are
the SchurLoc gauge units pushed into the coordinate ring by `C`. The unconditional conjugation; the
chart-locus normalization to `diag(I_r,0)` is downstream (it needs the Schur relation, modulo the
chart vanishing ideal). -/
theorem gaugeEquiv_endpointGauge_multPoly {N : ℕ} (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (rr : Fin (d (Fin.last (N + 1)))) (cc : Fin (d 0)) :
    gaugeEquiv d (endpointGauge (k := k) d r hp hq) (multPoly d rr cc)
      = (((Units.val (isUnit_Lmat (k := k) (d 0) (d (Fin.last (N + 1))) r hp).unit⁻¹).map
              (C : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →+* _)
            * Matrix.of (multPoly d)
            * (Units.val (isUnit_Hmat (k := k) (d 0) (d (Fin.last (N + 1))) r hq).unit⁻¹).map
              (C : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →+* _) :
          Matrix (Fin (d (Fin.last (N + 1)))) (Fin (d 0))
            (MvPolynomial (RepCoord d) (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)))
          rr cc) := by
  rw [gaugeEquiv_multPoly, liftGauge_endpointGauge_last d r hp hq,
    liftGauge_endpointGauge_zero_inv d r hp hq]

end DLNFibre.Core
