**Short Answer**

(A) Your route is right, but I would package steps 1, 2, and 4 into one reusable lemma for arbitrary `z : Localization.Away dsig`. You cannot really avoid numerator extraction; `Localization.Away` equality-to-zero is proved by clearing denominators, and Lean needs a representative at some point. The cleaner proof is to hide that inside:

```lean
theorem sigmaAway_eq_zero_of_forall_eval_zero
    (z : Localization.Away (chartDsig k d r hp hq))
    (hz : ∀ A, A ∈ productRankLocus d r →
      eval (canonicalCoord d A) (ΔPdeep d r hp hq) ≠ 0 →
      evalSigmaAway k d r hp hq A ‹_› ‹_› z = 0) :
    z = 0 := by
  -- mk'_surjective
  -- Ideal.Quotient.mk_surjective for the numerator
  -- split on Δ(A)=0 / Δ(A)≠0
  -- conclude f^m * a ∈ vanishingIdeal Σ
```

Then `chartPhi_vanishingIdeal_le` becomes: apply this lemma to `z := chartPhiFibAeval ... p`; the pointwise zero is exactly the Φ evaluation lemma plus `chartGauge_mem_fibre`.

The existing APIs you want are already used in the repo: `IsLocalization.mk'_surjective`, `IsLocalization.liftAlgHom`, `IsLocalization.lift_mk'_spec`, `Ideal.Quotient.mk_surjective`, and `Ideal.Quotient.eq_zero_iff_mem`; compare the Ψ proof in [ChartPsiDescent.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartPsiDescent.lean:75) and the zero-tests in [PrincipalOpenComorphism.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PrincipalOpenComorphism.lean:67).

**For Step 2**

Your current primitive is denominator-`1`. Add the denominator-power variant; it is the one that matches `mk'_surjective` directly:

```lean
theorem away_mk'_pow_eq_zero_iff_exists_pow_mul_mem
    (Z : Set (σ → k)) (f₀ a : MvPolynomial σ k) (n : ℕ) :
    IsLocalization.mk'
        (Localization.Away (Ideal.Quotient.mk (vanishingIdeal k Z) f₀))
        (Ideal.Quotient.mk (vanishingIdeal k Z) a)
        (⟨(Ideal.Quotient.mk (vanishingIdeal k Z) f₀) ^ n, n, rfl⟩ :
          Submonoid.powers (Ideal.Quotient.mk (vanishingIdeal k Z) f₀)) = 0
      ↔ ∃ m : ℕ, f₀ ^ m * a ∈ vanishingIdeal k Z := by
  rw [away_mk'_eq_zero_iff_exists_pow_mul_eq_zero]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rwa [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow]
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rwa [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
```

This is the most direct use of the Σ-side quotient structure.

**For (B)**

Yes, the Φ evaluation lemma mirrors cleanly, but define “A’s Schur data” explicitly rather than existentially:

```lean
noncomputable def schurOfMult (A : Tuple (k := k) d) :
    SchurVar (d 0) (d (Fin.last (N + 1))) r → k
  | Sum.inl (i, j) =>
      mult d A (Fin.castLE hp i) (Fin.castLE hq j)
  | Sum.inr (Sum.inl (i, b)) =>
      mult d A (Fin.castLE hp i)
        (Fin.cast (by omega) (Fin.natAdd r b))
  | Sum.inr (Sum.inr (a, j)) =>
      mult d A
        (Fin.cast (by omega) (Fin.natAdd r a))
        (Fin.castLE hq j)
```

Then prove:

```lean
theorem eval_schurOfMult_detSchurS :
    eval (schurOfMult d r hp hq A)
      (detSchurS (d 0) (d (Fin.last (N + 1))) r)
      =
    eval (canonicalCoord d A) (ΔPdeep d r hp hq)
```

or directly equals `(chartΔ (mult d A) hp hq).det`. Use `eval_det_submatrix_multPoly` plus `eval_multPoly`.

The Φ tower lemma should look like the Ψ one in [ChartEvalRealize.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartEvalRealize.lean:82), but with `sigmaCoordT`, `schurToDsig`, and `endpointGauge` not inverse:

```lean
theorem evalSigmaAway_chartPhiFibAeval ... :
    evalSigmaAway ... A hA hΔ (chartPhiFibAeval k d r hp hq p)
      =
    aeval (canonicalCoord d
      (baseChange
        (evalGauge (d 0) (d (Fin.last (N + 1))) r
          (schurEval _ _ _ (schurOfMult d r hp hq A) hs)
          (endpointGauge (k := k) d r hp hq))
        A)) p
```

Then prove the evaluated gauge is the concrete chart gauge:

```lean
theorem evalGauge_endpointGauge_eq_chartGauge :
    evalGauge ... (schurEval ... (schurOfMult ... A) hs)
        (endpointGauge (k := k) d r hp hq)
      =
    chartGauge d r hp hq (mult d A) hΔunit
```

That is the bridge allowing `chartGauge_mem_fibre`.

**For (C)**

The Φ descent itself should not need `[Infinite k]`. The Ψ side needed `[Infinite k]` because it used a coefficientwise polynomial zero-test via `MvPolynomial.funext`. The Φ side can prove membership in `vanishingIdeal` directly with:

```lean
rw [mem_vanishingIdeal_iff]
intro y hy
```

and split on `Δ(y) = 0`. No funext is involved. Keeping `[Infinite k]` in the public theorem is harmless for downstream symmetry, but it is not logically needed by this route.

**Most Likely Break**

(D) The fragile step is not the zero-test. It is:

```lean
evalGauge_endpointGauge_eq_chartGauge
```

because it crosses three representations of the same pivot data: `SchurLoc` variables, evaluated matrix blocks of `mult A`, and the concrete `Lmatk`/`Hmatk` used by `chartGauge`.

Use these APIs/patterns:

```lean
Localization.algHom_ext
MvPolynomial.algHom_ext'
MvPolynomial.algHom_ext
IsLocalization.liftAlgHom_apply
IsLocalization.lift_eq
Units.ext
Units.coe_map
Units.coe_map_inv
RingHom.map_det
Matrix.map_mul
Matrix.mul_nonsing_inv
Matrix.nonsing_inv_mul
Matrix.inv_eq_left_inv
```

For the descent proof itself, the clean APIs are `Ideal.Quotient.mk_surjective`, `Ideal.Quotient.eq_zero_iff_mem`, `mem_vanishingIdeal_iff`, and the generalized `away_mk'_pow_eq_zero_iff_exists_pow_mul_mem` above.
