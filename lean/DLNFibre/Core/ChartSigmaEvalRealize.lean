/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartSigmaEvalGauge
import DLNFibre.Core.ChartPhiFibCoord

/-!
# `DLNFibre.Core.ChartSigmaEvalRealize` — the Φ chart-evaluation lemma proper (seam D)

The source-side chart-evaluation lemma (mirror of the Ψ-side `ChartEvalRealize.evalAway_chartPsiAeval`,
with the FORWARD gauge): the chart-point evaluation `evalSigmaAway A` of the Φ fibre comorphism
`chartPhiFibAeval p` is `aeval` at the **evaluated-forward-gauge translate** of the chart point `A`:

> `evalSigmaAway A (chartPhiFibAeval p)
>     = aeval (canonicalCoord (baseChange (evalGauge (schurEval (schurOfMult A)) endpointGauge) A)) p`.

By `MvPolynomial.algHom_ext`: per generator, `evalSigmaAway (chartPhiFibSub x)` chains the tower
decomposition (`evalSigmaAway_comp_chartPhiTower`) and the gauge-evaluation commute
(`aevalTower_gaugeSub`, LANDED, at the **forward** `endpointGauge`).

## Main results
- `evalSigmaAway_comp_chartPhiTower` — `evalSigmaAway ∘ chartPhiTower = aevalTower (schurEval
  (schurOfMult A)) (canonicalCoord A)`.
- `evalSigmaAway_chartPhiFibAeval` — the chart-evaluation lemma proper.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

variable (k) in
/-- **The tower decomposition (source side).** `evalSigmaAway A ∘ chartPhiTower = aevalTower
(schurEval (schurOfMult A)) (canonicalCoord A)`: the source-side evaluation of the `SchurLoc`-
coefficient tower is the `aevalTower` evaluating `SchurLoc`-coefficients via the chart-point Schur
evaluation `schurEval (schurOfMult A)` and `RepCoord d` generators at the chart point `A`. By
`MvPolynomial.algHom_ext'` (coefficient leg `evalSigmaAway ∘ schurToDsig = schurEval`, variable leg
`evalSigmaAway ∘ sigmaCoordT = canonicalCoord A`). Mirror of `evalAway_comp_chartPsiTower`. -/
theorem evalSigmaAway_comp_chartPhiTower (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (A : Tuple (k := k) d) (hA : A ∈ productRankLocus d r)
    (hΔ : eval (canonicalCoord d A) (ΔPdeep d r hp hq) ≠ 0)
    (hs : eval (schurOfMult k d r hp hq A) (detSchurS (d 0) (d (Fin.last (N + 1))) r) ≠ 0) :
    (evalSigmaAway k d r hp hq A hA hΔ).comp (chartPhiTower k d r hp hq)
      = MvPolynomial.aevalTower
          (schurEval (k := k) (d 0) (d (Fin.last (N + 1))) r (schurOfMult k d r hp hq A) hs)
          (canonicalCoord d A) := by
  apply MvPolynomial.algHom_ext'
  · -- coefficient leg (`SchurLoc`-side): `evalSigmaAway ∘ schurToDsig = schurEval`.
    have hcoeff := evalSigmaAway_comp_schurToDsig (k := k) d r hp hq A hA hΔ hs
    rw [AlgHom.comp_assoc]
    rw [show (chartPhiTower k d r hp hq).comp
          (IsScalarTower.toAlgHom k (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
            (MvPolynomial (RepCoord d) (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)))
        = schurToDsig k d r hp hq from by
      rw [chartPhiTower]; exact MvPolynomial.aevalTower_comp_toAlgHom _ _]
    rw [hcoeff, MvPolynomial.aevalTower_comp_toAlgHom]
  · -- variable leg (`RepCoord d`-side): `evalSigmaAway (chartPhiTower (X x)) = canonicalCoord A x`.
    intro x
    rw [AlgHom.comp_apply, chartPhiTower, MvPolynomial.aevalTower_X, evalSigmaAway_sigmaCoordT,
      MvPolynomial.aevalTower_X]

variable (k) in
/-- **The Φ chart-evaluation lemma proper** (source side, mirror of `evalAway_chartPsiAeval`). The
source-side chart-point evaluation `evalSigmaAway A` of the Φ fibre comorphism `chartPhiFibAeval p`
is `aeval` at the evaluated-**forward**-gauge translate of the chart point `A`:

> `evalSigmaAway A (chartPhiFibAeval p)
>     = aeval (canonicalCoord (baseChange (evalGauge (schurEval (schurOfMult A)) endpointGauge) A)) p`.

By `MvPolynomial.algHom_ext`: per generator `x`, `evalSigmaAway (chartPhiFibSub x)` chains the tower
decomposition (`evalSigmaAway_comp_chartPhiTower`) and the gauge-evaluation commute
(`aevalTower_gaugeSub`, at the forward `endpointGauge`) to the `x`-coordinate of the evaluated-gauge
translate `baseChange (evalGauge (schurEval (schurOfMult A)) endpointGauge) A`. -/
theorem evalSigmaAway_chartPhiFibAeval (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (A : Tuple (k := k) d) (hA : A ∈ productRankLocus d r)
    (hΔ : eval (canonicalCoord d A) (ΔPdeep d r hp hq) ≠ 0)
    (hs : eval (schurOfMult k d r hp hq A) (detSchurS (d 0) (d (Fin.last (N + 1))) r) ≠ 0)
    (p : MvPolynomial (RepCoord d) k) :
    evalSigmaAway k d r hp hq A hA hΔ (chartPhiFibAeval k d r hp hq p)
      = aeval (canonicalCoord d
          (baseChange (evalGauge (d 0) (d (Fin.last (N + 1))) r
            (schurEval (d 0) (d (Fin.last (N + 1))) r (schurOfMult k d r hp hq A) hs)
            (endpointGauge (k := k) d r hp hq)) A)) p := by
  have key : (evalSigmaAway k d r hp hq A hA hΔ).comp (chartPhiFibAeval k d r hp hq)
      = (aeval (canonicalCoord d
          (baseChange (evalGauge (d 0) (d (Fin.last (N + 1))) r
            (schurEval (d 0) (d (Fin.last (N + 1))) r (schurOfMult k d r hp hq A) hs)
            (endpointGauge (k := k) d r hp hq)) A)) :
            MvPolynomial (RepCoord d) k →ₐ[k] k) := by
    apply MvPolynomial.algHom_ext
    intro x
    rw [AlgHom.comp_apply, chartPhiFibAeval, aeval_X, chartPhiFibSub, aeval_X]
    have htower := evalSigmaAway_comp_chartPhiTower (k := k) d r hp hq A hA hΔ hs
    rw [show evalSigmaAway k d r hp hq A hA hΔ
          (chartPhiTower k d r hp hq (gaugeSub d (endpointGauge (k := k) d r hp hq) x))
        = (evalSigmaAway k d r hp hq A hA hΔ).comp (chartPhiTower k d r hp hq)
            (gaugeSub d (endpointGauge (k := k) d r hp hq) x) from rfl, htower]
    rw [aevalTower_gaugeSub]
    exact (canonicalCoord_apply _ x).symm
  exact AlgHom.congr_fun key p

end DLNFibre.Core
