/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartSigmaGaugeBridge

/-!
# `DLNFibre.Core.ChartPhiDescent` — the Φ fibre comorphism descends (seam D, part 3)

The Φ-direction mirror of seam C's `ChartPsiDescent`. The Φ fibre comorphism `chartPhiFibAeval :
MvPolynomial (RepCoord d) k →ₐ[k] Localization.Away dsig` (LANDED, `ChartPhiFibCoord`) is **descended**
to the fibre coordinate ring `O(F)`:

1. `sigmaAway_eq_zero_of_forall_eval_zero` — the packaged Σ-side zero-test: an element `z` of the
   source localization `Away dsig` that vanishes under every chart-point evaluation `evalSigmaAway A`
   (`A ∈ Σ^r`, `ΔPdeep(A) ≠ 0`) is `0`. Numerator-extraction (`mk'_surjective`) + the denominator-power
   zero-test `away_mk'_pow_eq_zero_iff_exists_pow_mul_mem` + the `ΔPdeep(A)=0`/`≠0` split.
2. `chartPhi_vanishingIdeal_le` — the descent obligation `vanishingIdeal F ⊆ ker chartPhiFibAeval`: a
   `p` vanishing on the fibre `F` maps to `0`, because the chart-evaluation lemma realizes
   `evalSigmaAway A (chartPhiFibAeval p) = aeval (canonicalCoord (chartGauge(mult A) • A)) p`
   (the bridge `evalGauge_endpointGauge_eq_chartGauge`), and `chartGauge(mult A) • A ∈ F`
   (`chartGauge_mem_fibre`), where `p` vanishes.
3. `chartPhiCoeff : O(F) →ₐ[k] Away dsig` — the `Ideal.Quotient.liftₐ` descent.
4. `chartPhiAeval : MvPolynomial SchurVar O(F) →ₐ[k] Away dsig` — the `aevalTower` of `chartPhiCoeff`
   (coefficients) and `chartPhiVarSub` (variables). The full Φ comorphism.

(The unit fact for `gF` and the localized lift `chartPhiLoc` are downstream.)

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

variable (k) in
/-- **The packaged Σ-side away zero-test.** An element `z` of the source localization `Away dsig`
that vanishes under every chart-point evaluation `evalSigmaAway A` (over chart points `A ∈ Σ^r` with
`ΔPdeep(A) ≠ 0`) is `0`. Write `z = mk' (mk a) (dsig^n)` (`mk'_surjective`); by the denominator-power
zero-test it suffices that `ΔPdeep · a ∈ vanishingIdeal Σ^r`, i.e. it vanishes on every `A ∈ Σ^r`. On
the `ΔPdeep(A) = 0` locus the `ΔPdeep` factor kills it; on `ΔPdeep(A) ≠ 0` the `mk'` relation +
`evalSigmaAway A z = 0` force `eval (canonicalCoord A) a = 0`. -/
theorem sigmaAway_eq_zero_of_forall_eval_zero (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (z : Localization.Away (chartDsig k d r hp hq))
    (hz : ∀ (A : Tuple (k := k) d) (hA : A ∈ productRankLocus d r)
        (hΔ : eval (canonicalCoord d A) (ΔPdeep d r hp hq) ≠ 0),
      evalSigmaAway k d r hp hq A hA hΔ z = 0) :
    z = 0 := by
  -- write `z = mk' (mk_Σ a₀) (dsig ^ n)` for a numerator class and an integer power.
  obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, hzeq⟩ :=
    IsLocalization.mk'_surjective (Submonoid.powers (chartDsig k d r hp hq)) z
  dsimp only at hzeq
  -- the numerator class `x : O(Σ^r)` is `mk_Σ a₀` for some polynomial `a₀`.
  obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← hzeq]
  -- by the `chartDsig`-native denominator-power zero-test, reduce to
  -- `ΔPdeep ^ 1 * a₀ ∈ vanishingIdeal (sweepSigma)`.
  rw [away_chartDsig_pow_eq_zero_iff k d r hp hq a₀ n]
  refine ⟨1, ?_⟩
  simp only [pow_one]
  -- `ΔPdeep * a₀` vanishes on `canonicalCoord '' Σ^r`.
  rw [mem_vanishingIdeal_iff]
  rintro y ⟨A, hA, rfl⟩
  rw [aeval_eq_eval, map_mul]
  by_cases hΔ : eval (canonicalCoord d A) (ΔPdeep d r hp hq) = 0
  · -- `ΔPdeep(A) = 0` kills the product.
    rw [hΔ, zero_mul]
  · -- `ΔPdeep(A) ≠ 0`: `evalSigmaAway A z = 0` forces `eval (canonicalCoord A) a₀ = 0`.
    have hEvalA : eval (canonicalCoord d A) a₀ = 0 := by
      have hzx : evalSigmaAway k d r hp hq A hA hΔ
          (IsLocalization.mk' (Localization.Away (chartDsig k d r hp hq))
            (Ideal.Quotient.mk (vanishingIdeal k (sweepSigma k d r)) a₀)
            (⟨chartDsig k d r hp hq ^ n, n, rfl⟩ :
              Submonoid.powers (chartDsig k d r hp hq))) = 0 := by
        rw [hzeq]; exact hz A hA hΔ
      rw [evalSigmaAway, IsLocalization.liftAlgHom_apply, IsLocalization.lift_mk'_spec _ _ 0] at hzx
      -- `evalSigma A (mk a₀) = (evalSigma A dsig)^n * 0 = 0` (the `mk'`-relation, RHS `v = 0`).
      have hev : evalSigma k d r hp hq A hA
          (Ideal.Quotient.mk (vanishingIdeal k (sweepSigma k d r)) a₀) = 0 := by
        simpa using hzx
      -- `evalSigma A (mk a₀) = eval (canonicalCoord A) a₀`.
      rw [show evalSigma k d r hp hq A hA
            (Ideal.Quotient.mk (vanishingIdeal k (sweepSigma k d r)) a₀)
          = eval (canonicalCoord d A) a₀ from by
        rw [evalSigma, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk, RingHom.coe_coe]
        exact congrFun (MvPolynomial.aeval_eq_eval (canonicalCoord d A)) a₀] at hev
      exact hev
    rw [hEvalA, mul_zero]

variable (k) in
/-- **The Φ descent obligation** `vanishingIdeal F ⊆ ker chartPhiFibAeval`: a polynomial `p` vanishing
on the fibre `F` maps to `0` under the Φ fibre comorphism into `Localization.Away dsig`. By the
packaged Σ-side zero-test it suffices that `evalSigmaAway A (chartPhiFibAeval p) = 0` for every chart
point `A ∈ Σ^r` with `ΔPdeep(A) ≠ 0`. The chart-evaluation lemma + the gauge bridge realize this as
`aeval (canonicalCoord (chartGauge(mult A) • A)) p`, and `chartGauge(mult A) • A ∈ F`
(`chartGauge_mem_fibre`), where `p` vanishes. -/
theorem chartPhi_vanishingIdeal_le (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    vanishingIdeal k (sweepFibre k d r hp hq)
      ≤ RingHom.ker (chartPhiFibAeval k d r hp hq).toRingHom := by
  intro p hp_van
  rw [RingHom.mem_ker]
  change chartPhiFibAeval k d r hp hq p = 0
  apply sigmaAway_eq_zero_of_forall_eval_zero k d r hp hq
  intro A hA hΔ
  -- the schur data of `mult A` has nonzero schur determinant (= `ΔPdeep(A) ≠ 0`).
  have hs : eval (schurOfMult k d r hp hq A) (detSchurS (d 0) (d (Fin.last (N + 1))) r) ≠ 0 := by
    rw [eval_schurOfMult_detSchurS]
    -- `det (chartΔ (mult A)) = eval (canonicalCoord A) ΔPdeep` (`eval_det_submatrix_multPoly`).
    rwa [show (chartΔ (mult d A) hp hq).det = eval (canonicalCoord d A) (ΔPdeep d r hp hq) from by
      rw [ΔPdeep, eval_det_submatrix_multPoly]; rfl]
  -- the chart-evaluation lemma: `evalSigmaAway A (chartPhiFibAeval p) = aeval (canonicalCoord A') p`,
  -- where `A' = baseChange (evalGauge (schurEval (schurOfMult A)) endpointGauge) A`.
  rw [evalSigmaAway_chartPhiFibAeval k d r hp hq A hA hΔ hs]
  -- the bridge: the evaluated forward gauge is `chartGauge (mult A)`, so `A' = chartGauge(mult A) • A`.
  have hΔunit : IsUnit (chartΔ (mult d A) hp hq).det :=
    isUnit_det_chartΔ_mult d r hp hq A hs
  rw [evalGauge_endpointGauge_eq_chartGauge d r hp hq A hs hΔunit]
  -- `chartGauge(mult A) • A ∈ fibre (normalForm)` (`chartGauge_mem_fibre`), where `p` vanishes.
  have hAfibre : chartGauge d r hp hq (mult d A) hΔunit • A
      ∈ fibre d (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq) :=
    chartGauge_mem_fibre d r hp hq A hΔunit (le_of_eq (mem_productRankLocus.mp hA))
  have hmem : canonicalCoord d (chartGauge d r hp hq (mult d A) hΔunit • A)
      ∈ sweepFibre k d r hp hq := ⟨_, hAfibre, rfl⟩
  rw [aeval_eq_eval]
  exact (mem_vanishingIdeal_iff.mp hp_van) _ hmem

variable (k) in
/-- **The descended Φ fibre comorphism** `chartPhiCoeff : O(F) →ₐ[k] Localization.Away dsig`: the
`Ideal.Quotient.liftₐ` of `chartPhiFibAeval` through the descent obligation. -/
noncomputable def chartPhiCoeff (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    sweepFibreRing k d r hp hq →ₐ[k] Localization.Away (chartDsig k d r hp hq) :=
  Ideal.Quotient.liftₐ (vanishingIdeal k (sweepFibre k d r hp hq)) (chartPhiFibAeval k d r hp hq)
    (fun _ ha ↦ chartPhi_vanishingIdeal_le k d r hp hq ha)

variable (k) in
/-- **The Φ comorphism** `chartPhiAeval : MvPolynomial SchurVar O(F) →ₐ[k] Localization.Away dsig`:
the `aevalTower` of the descended fibre comorphism `chartPhiCoeff` (on `O(F)`-coefficients) and the
var leg `chartPhiVarSub` (on `SchurVar` generators). The Φ-direction comorphism. -/
noncomputable def chartPhiAeval (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) (sweepFibreRing k d r hp hq) →ₐ[k]
      Localization.Away (chartDsig k d r hp hq) :=
  MvPolynomial.aevalTower (chartPhiCoeff k d r hp hq) (chartPhiVarSub k d r hp hq)

end DLNFibre.Core
