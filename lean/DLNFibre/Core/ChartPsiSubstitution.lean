/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartSchurConnect
import DLNFibre.Core.ChartGaugeNormalize

/-!
# `DLNFibre.Core.ChartPsiSubstitution` — the Ψ-direction comorphism substitution (seam 3)

Seam 3 of the route-β localized chart `AlgEquiv` (thread 31, vehicle B): the comorphism substitution
of the inverse chart map `Ψ(M, B) = chartGauge(M)⁻¹ • B`, as a `k`-algebra hom
`MvPolynomial (RepCoord d) k →ₐ[k] Localization.Away gF`.

The map is built from the LANDED `SchurLoc`-coefficient gauge: `gaugeSub d (endpointGauge⁻¹)` sends
each coordinate to its inverse-gauged value over `MvPolynomial (RepCoord d) SchurLoc`; the
`SchurLoc`-coefficients are carried into the schur-side target `Localization.Away gF` by `schurToGfib`
(seam 2), and the `RepCoord d` generators map to the fibre-point coordinates `fibCoordT`. The
composite `aevalTower schurToGfib fibCoordT ∘ gaugeSub (endpointGauge⁻¹)` is the substitution, and
`chartPsiAeval = aeval` of it.

The mult-transport `gaugeEquiv_endpointGauge_multPoly` (step-3a, LANDED) carries the generic product
entry `multPoly r c` to `(Lmat⁻¹ · multPoly · Hmat⁻¹) r c` over `SchurLoc`; pushed through
`aevalTower schurToGfib fibCoordT`, this is the product-reconstruction the descent rides.

## Main results
- `fibCoordT` — the fibre-coordinate evaluator `RepCoord d → Localization.Away gF`.
- `chartPsiSub` / `chartPsiAeval` — the Ψ substitution and its `aeval` `k`-algebra hom.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

variable (k) in
/-- **The fibre-coordinate evaluator** `fibCoordT : RepCoord d → Localization.Away gF`: a coordinate
`x` maps to the `O(F)`-class of `X x`, pushed into the schur-side localization `Localization.Away gF`.
The image of the fibre point `B`'s coordinates under the comorphism. -/
noncomputable def fibCoordT (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    RepCoord d → Localization.Away (chartGfib k d r hp hq) :=
  fun x ↦ algebraMap (sweepFibreRing k d r hp hq) (Localization.Away (chartGfib k d r hp hq))
    (Ideal.Quotient.mk (vanishingIdeal k (sweepFibre k d r hp hq)) (X x))

variable (k) in
/-- The `SchurLoc`-coefficient evaluator `MvPolynomial (RepCoord d) SchurLoc →ₐ[k] Away gF`: the
`aevalTower` of the connecting map `schurToGfib` (on coefficients) and `fibCoordT` (on variables).
This carries the inverse-gauged generic factors (`SchurLoc`-coefficient polynomials) into the
schur-side target. -/
noncomputable def chartPsiTower (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    MvPolynomial (RepCoord d) (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) →ₐ[k]
      Localization.Away (chartGfib k d r hp hq) :=
  MvPolynomial.aevalTower (schurToGfib k d r hp hq) (fibCoordT k d r hp hq)

variable (k) in
/-- **The Ψ substitution** `chartPsiSub : RepCoord d → Localization.Away gF`: each coordinate `x`
maps to the inverse-gauged value `gaugeSub d (endpointGauge⁻¹) x` (a `SchurLoc`-coefficient
polynomial), carried into the target by `chartPsiTower`. The comorphism of
`Ψ(M, B) = chartGauge(M)⁻¹ • B`. -/
noncomputable def chartPsiSub (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    RepCoord d → Localization.Away (chartGfib k d r hp hq) :=
  fun x ↦ chartPsiTower k d r hp hq
    (gaugeSub d (endpointGauge (k := k) d r hp hq)⁻¹ x)

variable (k) in
/-- **The Ψ comorphism** `chartPsiAeval : MvPolynomial (RepCoord d) k →ₐ[k] Localization.Away gF`:
`aeval` of the Ψ substitution. The un-descended comorphism (the descent through `vanishingIdeal Σ^r`
and the localization lift are downstream). -/
noncomputable def chartPsiAeval (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    MvPolynomial (RepCoord d) k →ₐ[k] Localization.Away (chartGfib k d r hp hq) :=
  MvPolynomial.aeval (chartPsiSub k d r hp hq)

end DLNFibre.Core
