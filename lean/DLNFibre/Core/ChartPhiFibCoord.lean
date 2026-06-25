/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartPhiSubstitution
import DLNFibre.Core.ChartGaugeNormalize

/-!
# `DLNFibre.Core.ChartPhiFibCoord` — the forward-gauged fibre-coordinate map (seam D, part 2)

Seam D part 2 of the route-β localized chart `AlgEquiv` (thread 31), Φ direction — the mirror of
`ChartPsiSubstitution`'s `chartPsiTower`/`chartPsiSub`/`chartPsiAeval`, but using the **forward**
endpoint gauge `endpointGauge` (not its inverse) and landing in the **source** localization
`Localization.Away dsig`.

- `chartPhiTower := aevalTower schurToDsig sigmaCoordT : MvPolynomial (RepCoord d) SchurLoc →ₐ[k]
  Away dsig` — carries the `SchurLoc`-coefficient gauge polynomials into the source target (coeff leg
  `schurToDsig`, var leg `sigmaCoordT`). Mirror of `chartPsiTower`.
- `chartPhiFibSub x := chartPhiTower (gaugeSub d endpointGauge x)` — the forward-gauged source
  coordinate. The comorphism of the fibre factor `chartGauge(mult A) • A` of `Φ(A)`. Mirror of
  `chartPsiSub` (which uses `endpointGauge⁻¹`).
- `chartPhiFibAeval := aeval chartPhiFibSub : MvPolynomial (RepCoord d) k →ₐ[k] Away dsig` — the
  un-descended fibre-coordinate comorphism (the descent through `vanishingIdeal F` is downstream).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

variable (k) in
/-- **The `SchurLoc`-coefficient evaluator into the source localization** `chartPhiTower :
MvPolynomial (RepCoord d) SchurLoc →ₐ[k] Away dsig`: the `aevalTower` of the connecting map
`schurToDsig` (on coefficients) and `sigmaCoordT` (on variables). Carries the forward-gauged generic
factors (`SchurLoc`-coefficient polynomials) into the source target. Mirror of `chartPsiTower`. -/
noncomputable def chartPhiTower (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    MvPolynomial (RepCoord d) (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) →ₐ[k]
      Localization.Away (chartDsig k d r hp hq) :=
  MvPolynomial.aevalTower (schurToDsig k d r hp hq) (sigmaCoordT k d r hp hq)

variable (k) in
/-- **The Φ fibre-coordinate substitution** `chartPhiFibSub : RepCoord d → Away dsig`: each
coordinate `x` maps to the **forward**-gauged value `gaugeSub d endpointGauge x` (a `SchurLoc`-
coefficient polynomial), carried into the source target by `chartPhiTower`. The comorphism of the
fibre factor `chartGauge(mult A) • A` of `Φ(A)`. Mirror of `chartPsiSub` (`endpointGauge⁻¹`). -/
noncomputable def chartPhiFibSub (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    RepCoord d → Localization.Away (chartDsig k d r hp hq) :=
  fun x ↦ chartPhiTower k d r hp hq
    (gaugeSub d (endpointGauge (k := k) d r hp hq) x)

variable (k) in
/-- **The Φ fibre comorphism** `chartPhiFibAeval : MvPolynomial (RepCoord d) k →ₐ[k] Away dsig`:
`aeval` of the Φ fibre substitution. The un-descended comorphism (the descent through
`vanishingIdeal F` and the `aevalTower` assembly into `chartPhiAeval` are downstream). Mirror of
`chartPsiAeval`. -/
noncomputable def chartPhiFibAeval (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    MvPolynomial (RepCoord d) k →ₐ[k] Localization.Away (chartDsig k d r hp hq) :=
  MvPolynomial.aeval (chartPhiFibSub k d r hp hq)

end DLNFibre.Core
