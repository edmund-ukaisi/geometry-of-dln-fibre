/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartPsiSubstitution

/-!
# `DLNFibre.Core.ChartPsiReconstruct` — the Ψ comorphism factors through the gauge `AlgEquiv` (seam 3b)

A building block of the Ψ-direction descent (thread 31, vehicle B): the Ψ comorphism `chartPsiAeval`
factors as the `SchurLoc`-coefficient tower `chartPsiTower` applied to the **gauge `AlgEquiv`**
`gaugeEquiv (endpointGauge⁻¹)`:

> `chartPsiAeval p = chartPsiTower (gaugeEquiv (endpointGauge⁻¹) p)`.

This is pure `aeval` bookkeeping: `chartPsiAeval = aeval (chartPsiTower ∘ gaugeSub (endpointGauge⁻¹))`
and `chartPsiTower ∘ gaugeSub` factors through `aeval (gaugeSub) = gaugeEquiv` by
`MvPolynomial.comp_aeval_apply`. It reduces the Ψ product-reconstruction to the LANDED transport
`gaugeEquiv_multPoly` at the inverse gauge — the bridge the descent rides.

## Main results
- `chartPsiAeval_eq_tower_gaugeEquiv` — the factorization through the gauge `AlgEquiv`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

variable (k) in
/-- **The Ψ comorphism factors through the gauge `AlgEquiv`.** For a `SchurLoc`-coefficient input the
Ψ substitution is `chartPsiTower ∘ gaugeSub (endpointGauge⁻¹)`; `aeval` of that composite factors
through `aeval (gaugeSub) = gaugeEquiv` at the **ring-hom level** by `MvPolynomial.comp_eval₂Hom`
(scalar-free), with `chartPsiTower ∘ (algebraMap SchurLoc) = schurToGfib`
(`aevalTower_comp_algebraMap`). Stated on a `SchurLoc`-coefficient polynomial `p`:

> `chartPsiTower (gaugeEquiv (endpointGauge⁻¹) p) = eval₂Hom schurToGfib (chartPsiSub-blocks) p`,

the bridge that reduces the Ψ reconstruction to the LANDED `gaugeEquiv_multPoly` at the inverse
gauge. -/
theorem chartPsiTower_gaugeEquiv (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (p : MvPolynomial (RepCoord d) (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)) :
    chartPsiTower k d r hp hq (gaugeEquiv d (endpointGauge (k := k) d r hp hq)⁻¹ p)
      = MvPolynomial.eval₂Hom (schurToGfib k d r hp hq).toRingHom
          (fun x ↦ chartPsiTower k d r hp hq
            (gaugeSub d (endpointGauge (k := k) d r hp hq)⁻¹ x)) p := by
  -- `gaugeEquiv P p = aeval (gaugeSub P) p`; push `chartPsiTower` in via `map_aeval` (ring-hom level).
  rw [gaugeEquiv_apply]
  have hmap := MvPolynomial.map_aeval (gaugeSub d (endpointGauge (k := k) d r hp hq)⁻¹)
      (chartPsiTower k d r hp hq).toRingHom p
  rw [show (chartPsiTower k d r hp hq) (aeval (gaugeSub d (endpointGauge (k := k) d r hp hq)⁻¹) p)
      = (chartPsiTower k d r hp hq).toRingHom
          (aeval (gaugeSub d (endpointGauge (k := k) d r hp hq)⁻¹) p) from rfl, hmap]
  -- `chartPsiTower ∘ (algebraMap SchurLoc _) = schurToGfib` (the coefficient leg of `aevalTower`).
  have hco : (chartPsiTower k d r hp hq).toRingHom.comp
      (algebraMap (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
        (MvPolynomial (RepCoord d) (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)))
      = (schurToGfib k d r hp hq).toRingHom := by
    rw [chartPsiTower]
    exact MvPolynomial.aevalTower_comp_algebraMap _ _
  rw [hco]
  rfl

end DLNFibre.Core
