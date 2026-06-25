/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartPhiLoc
import DLNFibre.Core.ChartGaugeTower

/-!
# `DLNFibre.Core.ChartRoundTrip` — the seam-E round-trip leg lemmas (Φ ∘ Ψ side)

The tower-composition lemmas reducing the cross-ring round-trip `chartPhiLoc ∘ chartPsiLoc` (h2) to
the gauge group law (`ChartGaugeTower.aevalTower_gaugeSub_gaugeSub`), without opening localization
fractions (Codex `seam-e-roundtrip-answer`). The composite `chartPhiLoc ∘ chartPsiTower` is itself an
`aevalTower` (coefficient leg `schurToDsig`, variable leg `chartPhiFibSub`), so

> `chartPhiLoc (chartPsiSub x) = aevalTower schurToDsig chartPhiFibSub (gaugeSub d eg⁻¹ x)`,

and `chartPhiFibSub y = chartPhiTower (gaugeSub d eg y) = aevalTower schurToDsig sigmaCoordT
(gaugeSub d eg y)`, so the gauge group law at `eg⁻¹ * eg = 1` collapses it to `sigmaCoordT x`.

## Main results
- `chartPhiLoc_algebraMap`, `chartPhiLoc_comp_schurToGfib`, `chartPhiLoc_fibCoordT` — the legs.
- `chartPhiLoc_comp_chartPsiTower` — the composite is `aevalTower schurToDsig chartPhiFibSub`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

variable (k) in
/-- `chartPhiLoc` agrees with `chartPhiAeval` on `P`-classes (the away-lift fixes the structure
map). -/
theorem chartPhiLoc_algebraMap (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (p : MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) (sweepFibreRing k d r hp hq)) :
    chartPhiLoc k d r hp hq
        (algebraMap _ (Localization.Away (chartGfib k d r hp hq)) p)
      = chartPhiAeval k d r hp hq p := by
  rw [chartPhiLoc, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

variable (k) in
/-- **The coefficient leg `chartPhiLoc ∘ schurToGfib = schurToDsig`.** Both are `SchurLoc →ₐ[k] Away
dsig`; by `Localization.algHom_ext` it suffices on `MvPolynomial SchurVar k`-classes, where
`schurToGfib` sends `f` to `algebraMap (Away gF) (mapAlgHom (ofId) f)` (`schurToGfib_algebraMap`),
`chartPhiLoc` of which is `chartPhiAeval (mapAlgHom (ofId) f) = chartPhiSchurAeval f`
(`chartPhiLoc_algebraMap` + `chartPhiAeval_map_algebraMap`), matching `schurToDsig (algebraMap f) =
chartPhiSchurAeval f` (`schurToDsig_algebraMap`). -/
theorem chartPhiLoc_comp_schurToGfib (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    (chartPhiLoc k d r hp hq).comp (schurToGfib k d r hp hq)
      = schurToDsig k d r hp hq := by
  apply Localization.algHom_ext (Submonoid.powers (detSchurS (d 0) (d (Fin.last (N + 1))) r))
  apply MvPolynomial.algHom_ext
  intro s
  rw [AlgHom.comp_apply, AlgHom.comp_apply]
  show chartPhiLoc k d r hp hq (schurToGfib k d r hp hq
      (algebraMap _ (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) (X s)))
    = schurToDsig k d r hp hq
      (algebraMap _ (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) (X s))
  rw [schurToGfib_algebraMap, chartPhiLoc_algebraMap, schurToDsig_algebraMap,
    -- `mapAlgHom (ofId) (X s) = map (algebraMap k O(F)) (X s)`, so `chartPhiAeval` reads it.
    show (MvPolynomial.mapAlgHom (Algebra.ofId k (sweepFibreRing k d r hp hq))) (X s)
        = MvPolynomial.map (algebraMap k (sweepFibreRing k d r hp hq)) (X s) from rfl,
    chartPhiAeval_map_algebraMap]

variable (k) in
/-- **The variable leg `chartPhiLoc (fibCoordT x) = chartPhiFibSub x`.** `fibCoordT x = algebraMap
O(F) (Away gF) (mk_F (X x))` factors through `algebraMap P (Away gF) ∘ C`, so `chartPhiLoc` of it is
`chartPhiAeval (C (mk_F (X x))) = chartPhiCoeff (mk_F (X x)) = chartPhiFibAeval (X x) =
chartPhiFibSub x`. -/
theorem chartPhiLoc_fibCoordT (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (x : RepCoord d) :
    chartPhiLoc k d r hp hq (fibCoordT k d r hp hq x) = chartPhiFibSub k d r hp hq x := by
  rw [fibCoordT,
    show algebraMap (sweepFibreRing k d r hp hq) (Localization.Away (chartGfib k d r hp hq))
        (Ideal.Quotient.mk (vanishingIdeal k (sweepFibre k d r hp hq)) (X x))
      = algebraMap (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r)
          (sweepFibreRing k d r hp hq)) (Localization.Away (chartGfib k d r hp hq))
          (C (Ideal.Quotient.mk (vanishingIdeal k (sweepFibre k d r hp hq)) (X x))) from by
        rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply],
    chartPhiLoc_algebraMap, chartPhiAeval, MvPolynomial.aevalTower_C]
  -- `chartPhiCoeff (mk_F (X x)) = chartPhiFibAeval (X x) = chartPhiFibSub x`.
  rw [chartPhiCoeff, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk, RingHom.coe_coe,
    chartPhiFibAeval, aeval_X]

variable (k) in
/-- **The composite `chartPhiLoc ∘ chartPsiTower` is `aevalTower schurToDsig chartPhiFibSub`.** By
`MvPolynomial.algHom_ext'`: the coefficient leg is `chartPhiLoc ∘ schurToGfib = schurToDsig`
(`chartPhiLoc_comp_schurToGfib`); the variable leg is `chartPhiLoc (fibCoordT x) = chartPhiFibSub x`
(`chartPhiLoc_fibCoordT`). This turns the cross-ring round-trip into a single tower at `eg⁻¹ * eg`. -/
theorem chartPhiLoc_comp_chartPsiTower (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    (chartPhiLoc k d r hp hq).comp (chartPsiTower k d r hp hq)
      = MvPolynomial.aevalTower (schurToDsig k d r hp hq) (chartPhiFibSub k d r hp hq) := by
  apply MvPolynomial.algHom_ext'
  · -- coefficient leg: `chartPhiLoc ∘ schurToGfib = schurToDsig`.
    rw [AlgHom.comp_assoc]
    rw [show (chartPsiTower k d r hp hq).comp
          (IsScalarTower.toAlgHom k (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
            (MvPolynomial (RepCoord d) (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)))
        = schurToGfib k d r hp hq from by
      rw [chartPsiTower]; exact MvPolynomial.aevalTower_comp_toAlgHom _ _]
    rw [chartPhiLoc_comp_schurToGfib, MvPolynomial.aevalTower_comp_toAlgHom]
  · -- variable leg: `chartPhiLoc (chartPsiTower (X x)) = chartPhiFibSub x`.
    intro x
    rw [AlgHom.comp_apply, chartPsiTower, MvPolynomial.aevalTower_X, chartPhiLoc_fibCoordT,
      MvPolynomial.aevalTower_X]

variable (k) in
/-- **The h2 per-generator identity** `chartPhiLoc (chartPsiSub x) = sigmaCoordT x`. The composite
`chartPhiLoc ∘ chartPsiTower = aevalTower schurToDsig chartPhiFibSub`
(`chartPhiLoc_comp_chartPsiTower`), and `chartPhiFibSub y = aevalTower schurToDsig sigmaCoordT
(gaugeSub eg y)`, so the value is the nested `aevalTower` of gauges `eg⁻¹` (Ψ) and `eg` (Φ),
collapsing by the gauge group law `aevalTower_gaugeSub_gaugeSub` at `eg⁻¹ * eg = 1` to
`sigmaCoordT x`. -/
theorem chartPhiLoc_chartPsiSub (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (x : RepCoord d) :
    chartPhiLoc k d r hp hq (chartPsiSub k d r hp hq x) = sigmaCoordT k d r hp hq x := by
  rw [chartPsiSub,
    show chartPhiLoc k d r hp hq (chartPsiTower k d r hp hq
        (gaugeSub d (endpointGauge (k := k) d r hp hq)⁻¹ x))
      = (chartPhiLoc k d r hp hq).comp (chartPsiTower k d r hp hq)
          (gaugeSub d (endpointGauge (k := k) d r hp hq)⁻¹ x) from rfl,
    chartPhiLoc_comp_chartPsiTower]
  rw [show chartPhiFibSub k d r hp hq
        = (fun y ↦ MvPolynomial.aevalTower (schurToDsig k d r hp hq) (sigmaCoordT k d r hp hq)
            (gaugeSub d (endpointGauge (k := k) d r hp hq) y)) from by
      funext y; rw [chartPhiFibSub, chartPhiTower]]
  rw [aevalTower_gaugeSub_gaugeSub (schurToDsig k d r hp hq) d (sigmaCoordT k d r hp hq)
    (endpointGauge (k := k) d r hp hq) (endpointGauge (k := k) d r hp hq)⁻¹ x,
    inv_mul_cancel, gaugeSub_one, MvPolynomial.aevalTower_X]

end DLNFibre.Core
