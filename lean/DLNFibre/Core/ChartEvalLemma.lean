/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartEvalGauge

/-!
# `DLNFibre.Core.ChartEvalLemma` — the chart-evaluation tower legs (Ψ descent, seam A linchpin)

The two evaluation legs feeding the route-β chart-evaluation lemma (thread 31, Codex route-(b)). The
target-side evaluation `evalAway s B` of the `SchurLoc`-coefficient tower `chartPsiTower` decomposes
as the `aevalTower` evaluating `SchurLoc`-coefficients via the chart-point evaluation `schurEval`
and `RepCoord d` generators at the fibre point `B`:

> `evalAway ∘ chartPsiTower = aevalTower schurEval (canonicalCoord B)`.

This is the bridge between the symbolic `SchurLoc`-coefficient gauge and its `k`-valued evaluation:
the downstream chart-evaluation lemma applies it to `gaugeSub (endpointGauge⁻¹) x` and identifies
the result with the evaluated-gauge translate of `B` (at the **unit** level via `Units.map`, so never
invokes `Matrix.nonsing_inv` — the pattern the engine's `liftGauge` already uses).

The decomposition chains two legs (`MvPolynomial.algHom_ext'`):
- coefficient leg `evalAway ∘ schurToGfib = schurEval` (`ChartEvalGauge`);
- variable leg `evalAway ∘ fibCoordT = canonicalCoord B` (`evalAway_fibCoordT`, here).

## Main results
- `evalAway_fibCoordT` — the variable leg `evalAway (fibCoordT x) = (canonicalCoord B) x`.
- `evalAway_comp_chartPsiTower` — `evalAway ∘ chartPsiTower = aevalTower schurEval (canonicalCoord B)`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-- **The variable leg of the chart-point evaluation.** `evalAway (fibCoordT x) = (canonicalCoord B) x`:
the fibre-coordinate generator `fibCoordT x = algebraMap O(F) (Away gF) (mk (X x))` evaluates, under
the target-side `evalAway`, to the `x`-coordinate of the fibre point `B`. Routes through the scalar
tower `O(F) → P → Away gF` then `aevalTower_C` + `evalF_mk_X`. -/
@[simp] theorem evalAway_fibCoordT (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (s : SchurVar (d 0) (d (Fin.last (N + 1))) r → k)
    (B : Tuple (k := k) d) (hB : B ∈ fibre d (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq))
    (hs : eval s (detSchurS (d 0) (d (Fin.last (N + 1))) r) ≠ 0)
    (x : RepCoord d) :
    evalAway k d r hp hq s B hB hs (fibCoordT k d r hp hq x) = (canonicalCoord d B) x := by
  -- `fibCoordT x` is the `O(F)`-class of `X x`, pushed through `O(F) → P → Away gF`. Route the
  -- `evalAway` through the `algebraMap P (Away gF)` it lifts (`evalAway_algebraMap`), via the
  -- scalar tower `O(F) → P → Away gF`, then `aevalTower_C` reads off the coefficient `evalF B`.
  rw [fibCoordT,
    show algebraMap (sweepFibreRing k d r hp hq) (Localization.Away (chartGfib k d r hp hq))
        (Ideal.Quotient.mk (vanishingIdeal k (sweepFibre k d r hp hq)) (X x))
      = algebraMap (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r)
          (sweepFibreRing k d r hp hq)) (Localization.Away (chartGfib k d r hp hq))
          (C (Ideal.Quotient.mk (vanishingIdeal k (sweepFibre k d r hp hq)) (X x))) from by
        rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply],
    evalAway_algebraMap, evalP, MvPolynomial.aevalTower_C, evalF_mk_X, canonicalCoord_apply]

/-- **The tower decomposition.** `evalAway ∘ chartPsiTower = aevalTower schurEval (canonicalCoord B)`:
the target-side evaluation of the `SchurLoc`-coefficient tower is the `aevalTower` evaluating
`SchurLoc`-coefficients via the chart-point evaluation `schurEval` and `RepCoord d` generators at the
fibre point `B`. By `MvPolynomial.algHom_ext'` (coefficient leg `evalAway ∘ schurToGfib = schurEval`,
variable leg `evalAway ∘ fibCoordT = canonicalCoord B`). -/
theorem evalAway_comp_chartPsiTower (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (s : SchurVar (d 0) (d (Fin.last (N + 1))) r → k)
    (B : Tuple (k := k) d) (hB : B ∈ fibre d (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq))
    (hs : eval s (detSchurS (d 0) (d (Fin.last (N + 1))) r) ≠ 0) :
    (evalAway k d r hp hq s B hB hs).comp (chartPsiTower k d r hp hq)
      = MvPolynomial.aevalTower
          (schurEval (k := k) (d 0) (d (Fin.last (N + 1))) r s hs) (canonicalCoord d B) := by
  apply MvPolynomial.algHom_ext'
  · -- coefficient leg (`SchurLoc`-side): `evalAway ∘ schurToGfib = schurEval`.
    have hcoeff := evalAway_comp_schurToGfib (k := k) d r hp hq s B hB hs
    -- both legs' coefficient comps are `schurEval`; `chartPsiTower`'s coeff comp is `schurToGfib`.
    rw [AlgHom.comp_assoc]
    rw [show (chartPsiTower k d r hp hq).comp
          (IsScalarTower.toAlgHom k (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
            (MvPolynomial (RepCoord d) (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)))
        = schurToGfib k d r hp hq from by
      rw [chartPsiTower]; exact MvPolynomial.aevalTower_comp_toAlgHom _ _]
    rw [hcoeff, MvPolynomial.aevalTower_comp_toAlgHom]
  · -- variable leg (`RepCoord d`-side): `evalAway (chartPsiTower (X x)) = canonicalCoord B x`.
    intro x
    rw [AlgHom.comp_apply, chartPsiTower, MvPolynomial.aevalTower_X, evalAway_fibCoordT,
      MvPolynomial.aevalTower_X]

end DLNFibre.Core
