/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartSigmaEval

/-!
# `DLNFibre.Core.ChartSigmaEvalGauge` — the Σ-side coefficient leg (Φ descent, seam D)

The coefficient leg of the source-side chart-point evaluation (mirror of the Ψ-side
`ChartEvalGauge.evalAway_comp_schurToGfib`): the chart-point evaluation `evalSigmaAway A` reads
`SchurLoc`-coefficients through the chart-point Schur evaluation `schurEval (schurOfMult A)`:

> `evalSigmaAway A ∘ schurToDsig = schurEval (schurOfMult A)`.

`schurToDsig` is the `liftAlgHom` of `chartPhiSchurAeval = aeval chartPhiVarSub`; on a
`MvPolynomial SchurVar k`-class it is `chartPhiSchurAeval`, and `evalSigmaAway A` of the var leg
`chartPhiVarSub s` reads the corresponding block entry of `mult d A` — which is exactly
`schurOfMult A s = aeval (schurOfMult A) (X s)`.

## Main results
- `schurToDsig_algebraMap` — `schurToDsig (algebraMap f) = chartPhiSchurAeval f`.
- `evalSigmaAway_comp_schurToDsig` — the coefficient leg.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

variable (k) in
/-- **`schurToDsig` on the structure-map image.** `schurToDsig (algebraMap f) = chartPhiSchurAeval f`:
the connecting map (the `liftAlgHom` of `chartPhiSchurAeval` at the powers of `detSchurS`) agrees with
`chartPhiSchurAeval` on the away-localization structure map. -/
theorem schurToDsig_algebraMap (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (f : MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) k) :
    schurToDsig k d r hp hq
        (algebraMap _ (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) f)
      = chartPhiSchurAeval k d r hp hq f := by
  rw [schurToDsig, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

variable (k) in
/-- `evalSigmaAway A` reads a var-leg block entry as the corresponding entry of `mult d A`, matching
`schurOfMult A` on each `SchurVar` generator. The per-generator core of the coefficient leg. -/
theorem evalSigmaAway_chartPhiVarSub (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (A : Tuple (k := k) d) (hA : A ∈ productRankLocus d r)
    (hΔ : eval (canonicalCoord d A) (ΔPdeep d r hp hq) ≠ 0)
    (s : SchurVar (d 0) (d (Fin.last (N + 1))) r) :
    evalSigmaAway k d r hp hq A hA hΔ (chartPhiVarSub k d r hp hq s)
      = schurOfMult k d r hp hq A s := by
  -- `chartPhiVarSub s = algebraMap (mk (block-entry multPoly))`; `evalSigmaAway` reads it at `A`,
  -- giving `eval (canonicalCoord A) (multPoly block) = (mult A) block = schurOfMult A s`.
  have key : ∀ (rr : Fin (d (Fin.last (N + 1)))) (cc : Fin (d 0)),
      evalSigmaAway k d r hp hq A hA hΔ
          (algebraMap (sweepSigmaRing k d r) (Localization.Away (chartDsig k d r hp hq))
            (Ideal.Quotient.mk (vanishingIdeal k (sweepSigma k d r)) (multPoly d rr cc)))
        = mult d A rr cc := by
    intro rr cc
    rw [evalSigmaAway_algebraMap, evalSigma, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk,
      RingHom.coe_coe,
      show (aeval (canonicalCoord d A)) (multPoly d rr cc)
          = eval (canonicalCoord d A) (multPoly d rr cc)
        from congrFun (MvPolynomial.aeval_eq_eval (canonicalCoord d A)) _,
      eval_multPoly]
  obtain (⟨i, j⟩ | ⟨i, b⟩ | ⟨a, j⟩) := s <;>
    · rw [chartPhiVarSub]; rw [key]; rfl

variable (k) in
/-- **The coefficient leg of the Σ-side chart-point evaluation.** `evalSigmaAway A ∘ schurToDsig =
schurEval (schurOfMult A)`: the source-side evaluation reads `SchurLoc`-coefficients through the
chart-point Schur evaluation at `mult d A`'s block data. By `Localization.algHom_ext` (suffices on
`MvPolynomial SchurVar k`-classes): `schurToDsig` sends such a class to `chartPhiSchurAeval f`, and
`evalSigmaAway A` of `chartPhiVarSub`-images matches `aeval (schurOfMult A)` per generator. -/
theorem evalSigmaAway_comp_schurToDsig (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (A : Tuple (k := k) d) (hA : A ∈ productRankLocus d r)
    (hΔ : eval (canonicalCoord d A) (ΔPdeep d r hp hq) ≠ 0)
    (hs : eval (schurOfMult k d r hp hq A) (detSchurS (d 0) (d (Fin.last (N + 1))) r) ≠ 0) :
    (evalSigmaAway k d r hp hq A hA hΔ).comp (schurToDsig k d r hp hq)
      = schurEval (k := k) (d 0) (d (Fin.last (N + 1))) r (schurOfMult k d r hp hq A) hs := by
  apply Localization.algHom_ext (Submonoid.powers (detSchurS (d 0) (d (Fin.last (N + 1))) r))
  apply MvPolynomial.algHom_ext
  intro s
  rw [AlgHom.comp_apply, AlgHom.comp_apply]
  show evalSigmaAway k d r hp hq A hA hΔ (schurToDsig k d r hp hq
      (algebraMap _ (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) (X s)))
    = schurEval (k := k) (d 0) (d (Fin.last (N + 1))) r (schurOfMult k d r hp hq A) hs
      (algebraMap _ (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) (X s))
  rw [schurToDsig_algebraMap, chartPhiSchurAeval, aeval_X, evalSigmaAway_chartPhiVarSub,
    schurEval_algebraMap, aeval_X]

end DLNFibre.Core
