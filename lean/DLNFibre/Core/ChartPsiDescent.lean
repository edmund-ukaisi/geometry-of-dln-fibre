/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartPsiReconstruct
import DLNFibre.Core.PrincipalOpenComorphism
import DLNFibre.Core.ChartEvalRealize
import DLNFibre.Core.SchurFibreVanishing

/-!
# `DLNFibre.Core.ChartPsiDescent` — the Ψ comorphism descends + localizes (seam 4, Ψ side)

Seam 4 of the route-β localized chart `AlgEquiv` (thread 31, the hard rung), Ψ direction. The Ψ
comorphism `chartPsiAeval : MvPolynomial (RepCoord d) k →ₐ[k] Localization.Away gF` (LANDED,
`ChartPsiSubstitution`) is **descended** to the chart-closure coordinate ring `O(Σ^r)` and then
**localized** to `Localization.Away dsig`:

1. `chartPsi_vanishingIdeal_le` — the descent obligation `vanishingIdeal Σ^r ⊆ ker chartPsiAeval`
   (**PROVED**: `mk'`-surjectivity + the away zero-test + seam B; the chart-evaluation lemma
   `evalAway_chartPsiAeval` realizes the target point in `Σ^r`, with the `detSchurS`-vanishing locus
   cleared by the `gF` factor).
2. `chartPsiQuot : O(Σ^r) →ₐ[k] Away gF` — the `Ideal.Quotient.liftₐ` descent.

The localizing-element-unit fact (`chartPsi_dsig_isUnit`) and the localized lift (`chartPsiLoc`)
live downstream in `Core.ChartPsiDsigUnit` (the brick-4 determinant assembly), which imports this
module.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-- **The chart-point evaluation reads `O(F)`-coefficients through a fibre point.** For a fibre
point `B` with `canonicalCoord B = y ∈ F`, `evalP s B x = eval s (map (evalFibrePt hy) x)`: both
evaluate the `O(F)`-coefficients of `x` at `B`/`y` and the `SchurVar` generators at `s`. The
`evalP = aevalTower (evalF B) s = eval₂` form (`eval₂_eq_eval_map`), with `evalF B = evalFibrePt hy`
the same point-evaluation `liftₐ (aeval (canonicalCoord B))`. The bridge to seam B's double
evaluation. -/
theorem evalP_eq_eval_map_evalFibrePt (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (s : SchurVar (d 0) (d (Fin.last (N + 1))) r → k)
    (B : Tuple (k := k) d) (hB : B ∈ fibre d (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq))
    (hy : canonicalCoord d B ∈ sweepFibre k d r hp hq)
    (x : MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) (sweepFibreRing k d r hp hq)) :
    evalP k d r hp hq s B hB x
      = MvPolynomial.eval s (MvPolynomial.map (evalFibrePt hy).toRingHom x) := by
  rw [evalP]
  -- `aevalTower (evalF B) s x = eval₂ (evalF B) s x = eval s (map (evalF B) x)`.
  change MvPolynomial.eval₂ ((evalF k d r hp hq B hB : _ →+* k)) s x = _
  rw [MvPolynomial.eval₂_eq_eval_map]
  -- `evalF B = evalFibrePt hy`: both are `liftₐ (aeval (canonicalCoord B))` (proof-irrelevant).
  rfl

variable (k) in
/-- **The Ψ descent obligation** `vanishingIdeal Σ^r ⊆ ker chartPsiAeval`: a polynomial `p`
vanishing on the rank-`r` product locus `Σ^r` maps to `0` under the Ψ comorphism into
`Localization.Away gF`. By the chart-evaluation lemma the target-side point evaluation of
`chartPsiAeval p` reads `p` at the evaluated-gauge translate `A ∈ Σ^r`, so it vanishes; writing
`chartPsiAeval p = mk' x (gFⁿ)`, the schur-determinant factor `gF · x` then vanishes under all of
seam B's double evaluations (the `δ(s)=0` case killed by the `gF` factor, the `δ(s)≠0` case by the
localized chart evaluation), so `gF · x = 0` and the away zero-test gives `chartPsiAeval p = 0`. -/
theorem chartPsi_vanishingIdeal_le [Infinite k] (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    vanishingIdeal k (sweepSigma k d r)
      ≤ RingHom.ker (chartPsiAeval k d r hp hq).toRingHom := by
  intro p hp_van
  rw [RingHom.mem_ker]
  change chartPsiAeval k d r hp hq p = 0
  -- write `chartPsiAeval p = mk' x ⟨gF^n, n, rfl⟩` over the schur-side localization.
  set gF := chartGfib k d r hp hq with hgF
  obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, hz⟩ :=
    IsLocalization.mk'_surjective (Submonoid.powers gF) (chartPsiAeval k d r hp hq p)
  dsimp only at hz
  rw [← hz]
  -- it suffices that `gF * x = 0` in `P` (the away zero-test, with annihilating power `m = 1`).
  rw [away_mk'_eq_zero_iff_exists_pow_mul_eq_zero gF (Localization.Away gF) x n]
  refine ⟨1, ?_⟩
  rw [pow_one]
  -- `gF * x = 0` by the seam-B coefficientwise zero-test.
  apply mvpoly_eq_zero_of_forall_eval_fibre
  intro s y hy
  rw [map_mul, map_mul]
  -- `map (evalFibrePt y) gF = detSchurS` (the k-coefficients survive), so `eval s · = δ(s)`.
  have hcomp : (evalFibrePt hy).toRingHom.comp
      (algebraMap k (sweepFibreRing k d r hp hq)) = RingHom.id k := by
    ext c; simp
  have hgFmap : MvPolynomial.map (evalFibrePt hy).toRingHom gF
      = detSchurS (d 0) (d (Fin.last (N + 1))) r := by
    rw [hgF, chartGfib, MvPolynomial.map_map, hcomp, MvPolynomial.map_id]
  rw [hgFmap, MvPolynomial.eval_map]
  -- split on the schur determinant value `δ(s) = eval s detSchurS`.
  by_cases hs : MvPolynomial.eval s (detSchurS (d 0) (d (Fin.last (N + 1))) r) = 0
  · -- `δ(s) = 0` kills the product (the `gF` factor).
    rw [hs, zero_mul]
  · -- `δ(s) ≠ 0`: realize `y` as a fibre point `B` and run the localized chart evaluation.
    obtain ⟨B, hB, hByeq⟩ := hy
    subst hByeq
    have hyB : canonicalCoord d B ∈ sweepFibre k d r hp hq := ⟨B, hB, rfl⟩
    -- the second factor `eval s (map (evalFibrePt y) x) = evalP s B x = 0`.
    have hsB : eval s (detSchurS (d 0) (d (Fin.last (N + 1))) r) ≠ 0 := hs
    -- `evalAway s B (chartPsiAeval p) = aeval (canonicalCoord A) p`, `A ∈ Σ^r`, so `= 0`.
    have hAmem : baseChange (evalGauge (d 0) (d (Fin.last (N + 1))) r
          (schurEval (d 0) (d (Fin.last (N + 1))) r s hsB)
          (endpointGauge (k := k) d r hp hq)⁻¹) B ∈ productRankLocus d r :=
      chartEvalGauge_smul_mem_productRankLocus d r hp hq _ B hB
    have hChartZero : evalAway k d r hp hq s B hB hsB (chartPsiAeval k d r hp hq p) = 0 := by
      rw [evalAway_chartPsiAeval]
      -- `p` vanishes on `sweepSigma`, and `canonicalCoord A ∈ sweepSigma` since `A ∈ Σ^r`.
      have hccA : canonicalCoord d (baseChange (evalGauge (d 0) (d (Fin.last (N + 1))) r
          (schurEval (d 0) (d (Fin.last (N + 1))) r s hsB)
          (endpointGauge (k := k) d r hp hq)⁻¹) B) ∈ sweepSigma k d r := ⟨_, hAmem, rfl⟩
      rw [aeval_eq_eval]
      exact (mem_vanishingIdeal_iff.mp hp_van) _ hccA
    -- transport: `evalAway (mk' x ⟨gF^n⟩) = 0 ↔ evalP x = 0` (`lift_mk'_spec`, `v = 0`).
    have hEvalPx : evalP k d r hp hq s B hB x = 0 := by
      have hzx : evalAway k d r hp hq s B hB hsB
          (IsLocalization.mk' (Localization.Away gF) x (⟨gF ^ n, n, rfl⟩ : Submonoid.powers gF))
          = 0 := by rw [hz]; exact hChartZero
      rw [evalAway, IsLocalization.liftAlgHom_apply,
        IsLocalization.lift_mk'_spec _ _ 0] at hzx
      simpa using hzx
    -- conclude via the `evalP = eval ∘ map evalFibrePt` bridge; second factor is `evalP s B x = 0`.
    rw [← MvPolynomial.eval_map,
      ← evalP_eq_eval_map_evalFibrePt d r hp hq s B hB hyB x, hEvalPx, mul_zero]

variable (k) in
/-- **The descended Ψ comorphism** `chartPsiQuot : O(Σ^r) →ₐ[k] Localization.Away gF`: the
`Ideal.Quotient.liftₐ` of `chartPsiAeval` through the descent obligation
`chartPsi_vanishingIdeal_le`. -/
noncomputable def chartPsiQuot [Infinite k] (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    sweepSigmaRing k d r →ₐ[k] Localization.Away (chartGfib k d r hp hq) :=
  Ideal.Quotient.liftₐ (vanishingIdeal k (sweepSigma k d r)) (chartPsiAeval k d r hp hq)
    (fun _ ha ↦ chartPsi_vanishingIdeal_le k d r hp hq ha)

/-! The localizing-element-unit fact `chartPsi_dsig_isUnit` (the symbolic product-reconstruction =
`chartPsiAeval ΔPdeep` is a unit) and the localized comorphism `chartPsiLoc` live downstream in
`Core.ChartPsiDsigUnit` (the brick-4 determinant assembly, which imports this module). -/

end DLNFibre.Core
