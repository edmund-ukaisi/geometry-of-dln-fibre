/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.PrincipalOpenComorphism
import DLNFibre.Core.ChartPhiSubstitution

/-!
# `DLNFibre.Core.ChartSigmaAwayZero` — Σ-side away zero-test + the chart point's Schur data (seam D)

Two reusable pieces for the Φ descent (thread 31, seam D), both over the **source** localization
`Away dsig = Localization.Away dsig`, which localizes the `vanishingIdeal`-quotient `O(Σ^r)`:

- `away_mk'_pow_eq_zero_iff_exists_pow_mul_mem` — the **denominator-power** variant of the Σ-side
  zero-test (`PrincipalOpenComorphism.away_eq_zero_iff_exists_pow_mul_mem`): a fraction
  `mk'(mk_Σ a)(dsig^n)` is `0` iff some `ΔPdeep^m · a ∈ vanishingIdeal Σ^r`. This matches the shape
  `IsLocalization.mk'_surjective` produces (denominator a power of the localizing element).

- `schurOfMult A` — the **Schur data of a chart point** `A`: the block entries of the product
  matrix `mult d A` at the pivot / bordering indices, as a `SchurVar → k` assignment. The Φ-side
  analog of the Ψ-side's given `s`. `eval_schurOfMult_detSchurS` reads its schur determinant as the
  pivot minor `det (chartΔ (mult d A))`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-- **The denominator-power Σ-side away zero-test.** For `Z ⊆ (σ → k)`, the coordinate ring
`OZ = MvPolynomial σ k ⧸ vanishingIdeal Z`, a localizing lift `f₀` and numerator `a`: the fraction
`mk'(mk a)(mk f₀ ^ n)` is `0` in `Localization.Away (mk f₀)` exactly when some `f₀`-power kills `a`
modulo `vanishingIdeal Z`. The denominator-power form `IsLocalization.mk'_surjective` produces. -/
theorem away_mk'_pow_eq_zero_iff_exists_pow_mul_mem {σ : Type u} (Z : Set (σ → k))
    (f₀ a : MvPolynomial σ k) (n : ℕ) :
    (IsLocalization.mk' (Localization.Away (Ideal.Quotient.mk (vanishingIdeal k Z) f₀))
        (Ideal.Quotient.mk (vanishingIdeal k Z) a)
        (⟨(Ideal.Quotient.mk (vanishingIdeal k Z) f₀) ^ n, n, rfl⟩ :
          Submonoid.powers (Ideal.Quotient.mk (vanishingIdeal k Z) f₀)) = 0)
      ↔ ∃ m : ℕ, f₀ ^ m * a ∈ vanishingIdeal k Z := by
  rw [away_mk'_eq_zero_iff_exists_pow_mul_eq_zero (Ideal.Quotient.mk (vanishingIdeal k Z) f₀)
    (Localization.Away (Ideal.Quotient.mk (vanishingIdeal k Z) f₀))
    (Ideal.Quotient.mk (vanishingIdeal k Z) a) n]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rwa [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow]
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rwa [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]

variable (k) in
/-- **The `chartDsig`-native Σ-side away zero-test.** For the source localizing element
`dsig = chartDsig` (`= mk (vanishingIdeal sweepSigma) ΔPdeep`): `mk' (mk a) (dsig ^ n) = 0` iff some
`ΔPdeep`-power kills `a` modulo `vanishingIdeal sweepSigma`. Proved via the **abstract-base** away
zero-test `away_mk'_eq_zero_iff_exists_pow_mul_eq_zero` over `O(Σ)` (keeping `chartDsig` abstract — no
unfolding through the away-localization instances), then transporting `chartDsig ^ m * mk a = 0` to
`ΔPdeep ^ m * a ∈ vanishingIdeal sweepSigma` (`mk` a ring hom, `Quotient.eq_zero_iff_mem`). -/
theorem away_chartDsig_pow_eq_zero_iff (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (a : MvPolynomial (RepCoord d) k) (n : ℕ) :
    (IsLocalization.mk' (Localization.Away (chartDsig k d r hp hq))
        (Ideal.Quotient.mk (vanishingIdeal k (sweepSigma k d r)) a)
        (⟨chartDsig k d r hp hq ^ n, n, rfl⟩ : Submonoid.powers (chartDsig k d r hp hq)) = 0)
      ↔ ∃ m : ℕ, ΔPdeep d r hp hq ^ m * a ∈ vanishingIdeal k (sweepSigma k d r) := by
  rw [away_mk'_eq_zero_iff_exists_pow_mul_eq_zero (chartDsig k d r hp hq)
    (Localization.Away (chartDsig k d r hp hq))
    (Ideal.Quotient.mk (vanishingIdeal k (sweepSigma k d r)) a) n]
  -- `chartDsig ^ m * mk a = mk (ΔPdeep ^ m * a)` (ring hom), zero iff `ΔPdeep^m·a ∈ vanishingIdeal`.
  refine exists_congr (fun m ↦ ?_)
  rw [chartDsig, ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]

variable (k) in
/-- **The Schur data of a chart point** `A`: the `SchurVar → k` assignment reading the block entries
of the product matrix `mult d A` at the pivot rows/cols (`castLE`, the Δ-block) and the bordering
rows/cols (`natAdd`, the `B12`/`B21` blocks). The Φ-side analog of the Ψ-side's given chart point
`s`; the chart-evaluation of `chartPhiVarSub` reads this off `mult d A`. -/
noncomputable def schurOfMult (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (A : Tuple (k := k) d) :
    SchurVar (d 0) (d (Fin.last (N + 1))) r → k :=
  fun s ↦ match s with
    | Sum.inl (i, j) => mult d A (Fin.castLE hp i) (Fin.castLE hq j)
    | Sum.inr (Sum.inl (i, b)) =>
        mult d A (Fin.castLE hp i)
          (Fin.cast (show r + (d 0 - r) = d 0 by omega) (Fin.natAdd r b))
    | Sum.inr (Sum.inr (a, j)) =>
        mult d A (Fin.cast (show r + (d (Fin.last (N + 1)) - r) = d (Fin.last (N + 1)) by omega)
          (Fin.natAdd r a)) (Fin.castLE hq j)

variable (k) in
/-- The Schur data on a Δ-block generator `Sum.inl (i, j)` reads the pivot entry
`mult d A (castLE i) (castLE j)` of the product. -/
@[simp] theorem schurOfMult_inl (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (A : Tuple (k := k) d) (i j : Fin r) :
    schurOfMult k d r hp hq A (Sum.inl (i, j))
      = mult d A (Fin.castLE hp i) (Fin.castLE hq j) := rfl

variable (k) in
/-- **The Schur determinant at a chart point is the pivot minor of `mult d A`.**
`eval (schurOfMult A) detSchurS = det (chartΔ (mult d A))`: `detSchurS` is the determinant of the
Δ-coordinate matrix, and `schurOfMult A` reads each Δ-coordinate `Sum.inl (i, j)` as the
`(castLE i, castLE j)` entry of `mult d A`, i.e. the `(i, j)` entry of `chartΔ (mult d A)`. -/
theorem eval_schurOfMult_detSchurS (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (A : Tuple (k := k) d) :
    eval (schurOfMult k d r hp hq A) (detSchurS (d 0) (d (Fin.last (N + 1))) r)
      = (chartΔ (mult d A) hp hq).det := by
  rw [detSchurS, RingHom.map_det, chartΔ]
  congr 1
  funext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X,
    Matrix.submatrix_apply, schurOfMult_inl]

end DLNFibre.Core
