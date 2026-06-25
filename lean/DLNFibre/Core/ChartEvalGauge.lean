/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartPointEval

/-!
# `DLNFibre.Core.ChartEvalGauge` — the `SchurLoc → k` chart-point evaluation (Ψ descent, seam A.2)

The `SchurLoc`-coefficient evaluation underlying the route-(b) chart-evaluation lemma (thread 31,
Codex `chart-eval-lemma-answer`): at a Schur assignment `s : SchurVar → k` with `detSchurS s ≠ 0`,
the localizing element `detSchurS` evaluates to a unit, so the `k`-algebra map
`aeval s : MvPolynomial SchurVar k →ₐ[k] k` lifts across the away-localization to

> `schurEval s hs : SchurLoc →ₐ[k] k`.

This is the coefficient leg of the target-side evaluation `evalAway ∘ chartPsiTower`: by
construction `evalAway ∘ schurToGfib = schurEval` (the schur-side localizing element `gF` evaluates
to `eval s detSchurS`, matching `detSchurS`'s image), so the chart-point evaluation reads
`SchurLoc`-coefficients through `schurEval`.

## Main results
- `schurEval` — the `SchurLoc →ₐ[k] k` evaluation at `s` (when `detSchurS s ≠ 0`).
- `schurEval_algebraMap` — `schurEval` on a `MvPolynomial SchurVar k`-class is `aeval s`.
- `evalAway_comp_schurToGfib` — `evalAway ∘ schurToGfib = schurEval` (the coefficient leg).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-- **The `SchurLoc → k` evaluation at a chart point.** When `eval s detSchurS ≠ 0`, the localizing
element `detSchurS` maps to a unit under `aeval s`, so `aeval s : MvPolynomial SchurVar k →ₐ[k] k`
lifts across `SchurLoc = Localization.Away detSchurS` via `IsLocalization.liftAlgHom`. -/
noncomputable def schurEval (q p r : ℕ)
    (s : SchurVar q p r → k) (hs : eval s (detSchurS (k := k) q p r) ≠ 0) :
    SchurLoc (k := k) q p r →ₐ[k] k :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (detSchurS (k := k) q p r))
    (f := MvPolynomial.aeval s)
    (by
      rintro ⟨y, n, rfl⟩
      rw [map_pow]
      refine (?_ : IsUnit (aeval s (detSchurS (k := k) q p r))).pow n
      rw [show aeval s (detSchurS (k := k) q p r) = eval s (detSchurS (k := k) q p r) from by
        rw [aeval_eq_eval]]
      exact (isUnit_iff_ne_zero).mpr hs)

/-- `schurEval` on the away-localization structure-map image of `f : MvPolynomial SchurVar k` is
`aeval s f`. -/
@[simp] theorem schurEval_algebraMap (q p r : ℕ)
    (s : SchurVar q p r → k) (hs : eval s (detSchurS (k := k) q p r) ≠ 0)
    (f : MvPolynomial (SchurVar q p r) k) :
    schurEval (k := k) q p r s hs (algebraMap _ (SchurLoc (k := k) q p r) f) = aeval s f := by
  rw [schurEval, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

/-- **`schurToGfib` on the structure-map image.** `schurToGfib (algebraMap f) =
algebraMap (mapAlgHom (ofId k O(F)) f)`: the connecting map (the `Away.mapₐ` of the coefficient
base-change at `detSchurS`) sends a `MvPolynomial SchurVar k`-class to its `O(F)`-coefficient form,
pushed into the schur-side localization. The defining `IsLocalization.map_eq` of `Away.mapₐ`. -/
theorem schurToGfib_algebraMap (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (f : MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) k) :
    schurToGfib k d r hp hq
        (algebraMap _ (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) f)
      = algebraMap _ (Localization.Away (chartGfib k d r hp hq))
          (MvPolynomial.mapAlgHom (Algebra.ofId k (sweepFibreRing k d r hp hq)) f) := by
  haveI : IsLocalization.Away
      (MvPolynomial.mapAlgHom (σ := SchurVar (d 0) (d (Fin.last (N + 1))) r)
        (Algebra.ofId k (sweepFibreRing k d r hp hq))
        (detSchurS (d 0) (d (Fin.last (N + 1))) r))
      (Localization.Away (chartGfib k d r hp hq)) := by
    rw [mapAlgHom_ofId_detSchurS (k := k) d r hp hq]; infer_instance
  rw [schurToGfib, IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map, IsLocalization.map_eq]
  rfl

/-- **The coefficient leg of the chart-point evaluation.** `evalAway ∘ schurToGfib = schurEval`: the
target-side evaluation reads `SchurLoc`-coefficients through the chart-point evaluation `schurEval`.
By `Localization.algHom_ext` (suffices on `MvPolynomial SchurVar k`-classes): `schurToGfib` sends
such a class to `algebraMap _ (Away gF) (mapAlgHom (ofId) f)`, and `evalAway` of that is
`evalP (mapAlgHom (ofId) f) = aeval s f` (the `O(F)`-coeffs collapse to `k` under `evalF`). -/
theorem evalAway_comp_schurToGfib (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (s : SchurVar (d 0) (d (Fin.last (N + 1))) r → k)
    (B : Tuple (k := k) d) (hB : B ∈ fibre d (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq))
    (hs : eval s (detSchurS (d 0) (d (Fin.last (N + 1))) r) ≠ 0) :
    (evalAway k d r hp hq s B hB hs).comp (schurToGfib k d r hp hq)
      = schurEval (k := k) (d 0) (d (Fin.last (N + 1))) r s hs := by
  -- both are `SchurLoc = Localization (powers detSchurS) →ₐ[k] k`; compare after precomposing with
  -- the structure map (`Localization.algHom_ext`), then on `MvPolynomial SchurVar k` generators.
  apply Localization.algHom_ext (Submonoid.powers (detSchurS (d 0) (d (Fin.last (N + 1))) r))
  apply MvPolynomial.algHom_ext
  intro x
  -- LHS: `schurToGfib ∘ algebraMap = algebraMap ∘ mapAlgHom`, then `evalAway ∘ algebraMap = evalP`.
  rw [AlgHom.comp_apply, AlgHom.comp_apply]
  show evalAway k d r hp hq s B hB hs (schurToGfib k d r hp hq
      (algebraMap _ (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) (X x)))
    = schurEval (k := k) (d 0) (d (Fin.last (N + 1))) r s hs
      (algebraMap _ (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) (X x))
  rw [schurToGfib_algebraMap, evalAway_algebraMap, evalP, schurEval_algebraMap]
  rw [show (MvPolynomial.mapAlgHom (Algebra.ofId k (sweepFibreRing k d r hp hq))) (X x)
      = MvPolynomial.map (algebraMap k (sweepFibreRing k d r hp hq)) (X x) from rfl,
    MvPolynomial.map_X]
  simp only [aevalTower_X, aeval_X]

end DLNFibre.Core
