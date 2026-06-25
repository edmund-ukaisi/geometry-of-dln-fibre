/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartSigmaAwayZero
import DLNFibre.Core.ChartEvalGaugeCommute

/-!
# `DLNFibre.Core.ChartSigmaEval` — the Σ-side chart-point evaluation (Φ descent, seam D)

The source-side evaluation maps, mirroring the Ψ-side `ChartPointEval`/`ChartEvalGauge`: a `k`-point
of the source localization `Away dsig` (which localizes `O(Σ^r)`) is a chart tuple `A ∈ Σ^r` with
`ΔPdeep(A) ≠ 0`. The chart point `A` evaluates the `O(Σ^r)`-classes (`evalSigma A`), and when
`ΔPdeep(A) ≠ 0` the localizing element `dsig` maps to a unit, so `evalSigma A` lifts across the
away-localization to `evalSigmaAway A : Away dsig →ₐ[k] k`.

The coefficient leg `evalSigmaAway A ∘ schurToDsig = schurEval (schurOfMult A)` (the chart-point
evaluation reads `SchurLoc`-coefficients through the Schur data of `mult A`) reuses the Ψ-side's
`schurEval`; the var leg `evalSigmaAway A (sigmaCoordT x) = canonicalCoord A x` is immediate.

## Main results
- `evalSigma` — the chart-point evaluation `O(Σ^r) →ₐ[k] k`.
- `evalSigma_dsig` — `evalSigma A dsig = eval (canonicalCoord A) ΔPdeep` (the localizing value).
- `evalSigmaAway` — the localized chart-point evaluation `Away dsig →ₐ[k] k`.
- `evalSigmaAway_comp_schurToDsig` — the coefficient leg.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

variable (k) in
/-- **The chart-point evaluation** `evalSigma A hA : O(Σ^r) →ₐ[k] k`: for a chart point `A ∈ Σ^r`,
the `Ideal.Quotient.liftₐ` of `aeval (canonicalCoord d A)`, which kills `vanishingIdeal Σ^r` because
`canonicalCoord d A ∈ Σ^r` (as a coordinate set). Reads the `O(Σ^r)`-class at `A`. -/
noncomputable def evalSigma (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (A : Tuple (k := k) d) (hA : A ∈ productRankLocus d r) :
    sweepSigmaRing k d r →ₐ[k] k :=
  Ideal.Quotient.liftₐ (vanishingIdeal k (sweepSigma k d r))
    (aeval (canonicalCoord d A))
    (fun a ha ↦ by
      have : canonicalCoord d A ∈ sweepSigma k d r := ⟨A, hA, rfl⟩
      exact (mem_vanishingIdeal_iff.mp ha) _ this)

variable (k) in
/-- `evalSigma A` reads the class of a coordinate `X x` as the entry `A x.1 x.2.1 x.2.2`. -/
@[simp] theorem evalSigma_mk_X (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (A : Tuple (k := k) d) (hA : A ∈ productRankLocus d r) (x : RepCoord d) :
    evalSigma k d r hp hq A hA (Ideal.Quotient.mk (vanishingIdeal k (sweepSigma k d r)) (X x))
      = A x.1 x.2.1 x.2.2 := by
  rw [evalSigma, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  simp only [RingHom.coe_coe, aeval_X, canonicalCoord_apply]

variable (k) in
/-- **The localizing element's value.** `evalSigma A dsig = eval (canonicalCoord A) ΔPdeep`: the
source localizing element `dsig = mk ΔPdeep` evaluates, under the chart-point evaluation, to the deep
pivot minor of the product `mult d A`. The bridge to the unit hypothesis for the away-lift. -/
theorem evalSigma_dsig (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (A : Tuple (k := k) d) (hA : A ∈ productRankLocus d r) :
    evalSigma k d r hp hq A hA (chartDsig k d r hp hq)
      = eval (canonicalCoord d A) (ΔPdeep d r hp hq) := by
  rw [chartDsig, evalSigma, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  rw [RingHom.coe_coe]
  exact congrFun (MvPolynomial.aeval_eq_eval (canonicalCoord d A)) (ΔPdeep d r hp hq)

variable (k) in
/-- **The localized chart-point evaluation** `evalSigmaAway A hA hΔ : Away dsig →ₐ[k] k`: when the
deep pivot minor is nonzero at `A` (`eval (canonicalCoord A) ΔPdeep ≠ 0`), the localizing element
`dsig` maps to a unit (`evalSigma_dsig` + field), so `evalSigma A` lifts across the away-localization
via `IsLocalization.liftAlgHom`. The `k`-point of the principal open `D(dsig)` for `A`. -/
noncomputable def evalSigmaAway (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (A : Tuple (k := k) d) (hA : A ∈ productRankLocus d r)
    (hΔ : eval (canonicalCoord d A) (ΔPdeep d r hp hq) ≠ 0) :
    Localization.Away (chartDsig k d r hp hq) →ₐ[k] k :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (chartDsig k d r hp hq))
    (f := evalSigma k d r hp hq A hA)
    (by
      rintro ⟨y, n, rfl⟩
      rw [map_pow]
      refine (?_ : IsUnit (evalSigma k d r hp hq A hA (chartDsig k d r hp hq))).pow n
      rw [evalSigma_dsig]
      exact (isUnit_iff_ne_zero).mpr hΔ)

variable (k) in
/-- `evalSigmaAway` agrees with `evalSigma` on `O(Σ^r)`-classes (the away-lift fixes the structure
map). -/
@[simp] theorem evalSigmaAway_algebraMap (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (A : Tuple (k := k) d) (hA : A ∈ productRankLocus d r)
    (hΔ : eval (canonicalCoord d A) (ΔPdeep d r hp hq) ≠ 0)
    (a : sweepSigmaRing k d r) :
    evalSigmaAway k d r hp hq A hA hΔ
        (algebraMap _ (Localization.Away (chartDsig k d r hp hq)) a)
      = evalSigma k d r hp hq A hA a := by
  rw [evalSigmaAway, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

variable (k) in
/-- **The var leg of the chart-point evaluation.** `evalSigmaAway A (sigmaCoordT x) = canonicalCoord
A x`: the source-coordinate embedding `sigmaCoordT x = algebraMap (mk (X x))` evaluates at the chart
point `A` to the `x`-coordinate of `A`. -/
@[simp] theorem evalSigmaAway_sigmaCoordT (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (A : Tuple (k := k) d) (hA : A ∈ productRankLocus d r)
    (hΔ : eval (canonicalCoord d A) (ΔPdeep d r hp hq) ≠ 0) (x : RepCoord d) :
    evalSigmaAway k d r hp hq A hA hΔ (sigmaCoordT k d r hp hq x) = canonicalCoord d A x := by
  rw [sigmaCoordT, evalSigmaAway_algebraMap, evalSigma_mk_X, canonicalCoord_apply]

end DLNFibre.Core
