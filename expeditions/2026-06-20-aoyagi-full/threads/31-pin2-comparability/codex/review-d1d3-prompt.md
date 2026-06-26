You are a decorrelated second-opinion reviewer (red-team) on a Lean 4 + Mathlib formalisation. Two soundness questions. Reason from Lean/Mathlib semantics. Distinguish what you can VERIFY from what you INFER. Be terse and object-level.

=== DELIVERABLE #1: a `change`-based measurability proof ===

Context: inside a larger proof, the goal at one point (after `rw [hΦscore, hScoreDef]` then `Measurable.add` splitting off a reg-sum term) is to show measurability of the "Score" summand. The proof does:

```
set Mw : (Fin (flatDim H) → ℝ) → Matrix (Fin r ⊕ Fin (H 0 - r)) (Fin r ⊕ Fin (H (Fin.last L) - r)) ℝ :=
  fun w => Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
    (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
    (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm w) - B) * endpointQL H hL Qf)
  with hMw_def
-- ... measurability bricks hb22 hb21 hb12 hInv hb11cont ...
change Measurable fun w => ∑ i, ∑ j,
  ((Mw w).toBlocks₂₂ - (Mw w).toBlocks₂₁ * ((Mw w).toBlocks₁₁ + 1)⁻¹ * (Mw w).toBlocks₁₂) i j ^ 2
-- ... then proves THAT goal ...
```

The `Score` being measured is defined (verbatim) as: `fun w => ∑ i, ∑ j, (( REINDEX_EXPR .toBlocks₂₂ - REINDEX_EXPR .toBlocks₂₁ * (REINDEX_EXPR .toBlocks₁₁ + 1)⁻¹ * REINDEX_EXPR .toBlocks₁₂) i j) ^ 2`, where REINDEX_EXPR is exactly the body of `Mw w` (same `Matrix.reindex (...) (endpointP0 ... * (prod ... - B) * endpointQL ...)`), occurring 4 times.

Q1: `set Mw := <body>` rewrites every syntactic occurrence of `<body>` in the goal to `Mw w`. Then `change <target>` succeeds only if `<target>` is DEFINITIONALLY equal to the current goal. Question: can the `change` here "mask a wrong statement" — i.e. could the proof end up proving measurability of a DIFFERENT function than the actual `Score` that the outer lemma (`rlctAtOn_squeeze`, which needs `Measurable Φscore` where `Φscore w = regSum w + Score w`) consumes? Or is it forced to be the same function because `change` is checked by defeq against the real goal? Address specifically whether `change` can ever weaken/alter the statement being proved.

Q2 (inverse-entry soundness): one brick proves `Measurable (fun w => ((Mw w).toBlocks₁₁ + 1)⁻¹ k l)` by rewriting via `Matrix.inv_def` (`A⁻¹ = Ring.inverse A.det • A.adjugate`) to `Ring.inverse ((..).det) * (..).adjugate k l`, using `Continuous.matrix_det`, `Continuous.matrix_adjugate`, and `Ring.inverse_eq_inv'` + `measurable_inv` for `Measurable (Ring.inverse : ℝ → ℝ)`. Is this sound? Any gap (e.g. does `Ring.inverse` on a field match `Inv.inv` everywhere incl. at 0)?

=== DELIVERABLE #3: a conditional reduction lemma ===

```
theorem rlctAtOn_diffeo_bridge_of {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℝ M] [MeasureSpace M] [BorelSpace M]
    [FiniteDimensional ℝ M] [(volume : Measure M).IsAddHaarMeasure]
    (Φscore Φcore : M → ℝ) (wstar : M) (Psi : M → M) (e : M ≃L[ℝ] M)
    (hcontdiff : ContDiff ℝ (⊤ : ℕ∞) Psi)
    (hderiv : HasStrictFDerivAt Psi (e : M →L[ℝ] M) wstar)
    (hfix : Psi wstar = wstar)
    (hcomp : (fun x => Φcore (Psi x)) =ᶠ[nhds wstar] Φscore) :
    rlctAtOn Φscore wstar = rlctAtOn Φcore wstar := by
  rw [← rlctAtOn_germ_local (fun x => Φcore (Psi x)) Φscore wstar hcomp]
  exact rlctAtOn_comp_localDiffeo Φcore wstar Psi e hcontdiff hderiv hfix
```

where:
- `rlctAtOn_germ_local (F G : N → ℝ) (w0) (hFG : F =ᶠ[nhds w0] G) : rlctAtOn F w0 = rlctAtOn G w0`
- `rlctAtOn_comp_localDiffeo (F) (wstar) (f : M→M) (e : M ≃L[ℝ] M) (hcontdiff : ContDiff ℝ ⊤ f) (hf : HasStrictFDerivAt f e wstar) (hfix : f wstar = wstar) : rlctAtOn (fun w => F (f w)) wstar = rlctAtOn F wstar`

Q3: Is this reduction CIRCULAR? I.e. do the hypotheses `(hcomp : Φcore∘Psi =ᶠ Φscore)` + the local-diffeo facts secretly presuppose the conclusion `rlctAtOn Φscore wstar = rlctAtOn Φcore wstar`, or do they encode genuinely WEAKER/DIFFERENT geometric content (a reparametrization + a germ identity) from which the RLCT-equality is DERIVED? Confirm the `rw [←...]` then `exact` composition typechecks to the stated conclusion (check the function shapes match: does `rlctAtOn_comp_localDiffeo`'s conclusion `rlctAtOn (fun w => Φcore (Psi w)) wstar` syntactically match what the `rw [←germ_local]` leaves as the goal LHS?).

Q4: Any way the lemma is VACUOUS (hypotheses unsatisfiable in a way that makes it trivially true / useless), or any overclaim in its statement vs. "a conditional reduction that defers the geometry to the consumer"?
