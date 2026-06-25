## Seam-B zero-test (PROVED):

`mvpoly_eq_zero_of_forall_eval_fibre : [Infinite k] → (h : MvPolynomial σ O(F)) →
   (∀ (s : σ → k) (y : τ → k) (hy : y ∈ F),
       eval s (map (evalFibrePt hy) h) = 0) → h = 0`,
i.e. a poly over O(F) is 0 if its double evaluation (O(F)-coeffs at any fibre point y, then σ-vars
at any s) vanishes for ALL s (including s where detSchurS s = 0).

## Away zero-test (PROVED):

`away_mk'_eq_zero_iff_exists_pow_mul_eq_zero {P} [CommRing P] (g : P) (S) [Away g S] (x : P) (n : ℕ) :
   IsLocalization.mk' S x ⟨g^n, n, rfl⟩ = 0 ↔ ∃ m : ℕ, g^m * x = 0`.

## THE OBLIGATION I want to discharge:

`chartPsi_vanishingIdeal_le : vanishingIdeal Σ ≤ RingHom.ker chartPsiAeval.toRingHom`,
i.e. for `p ∈ vanishingIdeal Σ`, `chartPsiAeval p = 0` in `Away gF`.

## My planned proof:

1. `z := chartPsiAeval p : Away gF`. By `IsLocalization.mk'_surjective (.powers gF)`, write
   `z = mk' x ⟨gF^n, n, rfl⟩` for some `x : P`, `n : ℕ`.
2. Goal `z = 0` ⟺ (zero-test) `∃ m, gF^m * x = 0`. I claim `m = 1` works: `gF * x = 0`.
3. `gF * x = 0` by seam B: for all `s : SchurVar → k`, `y ∈ F`, show
   `eval s (map (evalFibrePt y) (gF * x)) = 0`.
   - `map (evalFibrePt y) (gF * x) = map(...)(gF) * map(...)(x)` (ring hom).
   - `eval s (map (evalFibrePt y) gF) = eval s detSchurS` (since gF's coeffs are k-constants;
     evalFibrePt y kills the O(F)-lift back to k). Call this `δ(s) := eval s detSchurS`.
   - So the integrand is `δ(s) * eval s (map (evalFibrePt y) x)`.
   - CASE δ(s) = 0: integrand = 0. Done.
   - CASE δ(s) ≠ 0: I must show `eval s (map (evalFibrePt y) x) = 0`. Here y ∈ F, so `B := the tuple
     with canonicalCoord B = y` is in `fibre E` (F = canonicalCoord '' fibre E), and I can form
     `evalAway s B hs` with `hs : δ(s) ≠ 0`. Now `evalAway s B hs z = 0` by (*). And
     `z = mk' x ⟨gF^n⟩`, so `evalAway z = evalP x / (evalP gF)^n = evalP x / δ(s)^n`. Since the
     denominator is a unit (δ(s) ≠ 0) and `evalAway z = 0`, we get `evalP x = 0`. Finally I claim
     `evalP s B x = eval s (map (evalFibrePt y) x)` (both evaluate O(F)-coeffs at B/y, SchurVar at s),
     which gives the seam-B integrand = 0.

## My questions:

Q1. Is the case-split argument in step 3 sound? In particular, the seam-B hypothesis quantifies over
ALL s, but `evalAway`/`evalP` only exist when δ(s) ≠ 0 — I handle δ(s)=0 by the `gF·` factor killing
it. Is `m=1` (one factor of gF) enough, or do I need more? (I believe 1 is enough since the factor
is `δ(s)^1`, and δ(s)=0 ⟹ whole product 0.)

Q2. The identity `evalP s B x = eval s (map (evalFibrePt (canonicalCoord B ∈ F)) x)` for `x : P =
MvPolynomial SchurVar O(F)`: `evalP = aevalTower (evalF B) s`. Is this just
`MvPolynomial.eval_map` / `aeval`-`eval` bookkeeping? `evalF B` and `evalFibrePt (cc B)` are both the
O(F)→k point-evaluation at B — are they DEFINITIONALLY equal or do I need a `congr` lemma? `evalF B :=
liftₐ (aeval (canonicalCoord B))`, `evalFibrePt hy := liftₐ (aeval y)`. With `y = canonicalCoord B`
these are the SAME liftₐ — so `evalF B = evalFibrePt (⟨B, hB, rfl⟩ : canonicalCoord B ∈ F)`? Confirm.

Q3. To extract `evalP x = 0` from `evalAway (mk' x ⟨gF^n⟩) = 0` with δ(s)≠0: what is the cleanest
Mathlib path? `evalAway` is `IsLocalization.liftAlgHom`; `IsLocalization.lift_mk'` gives
`lift f (mk' x sm) = f x * (IsUnit.unit (hf sm))⁻¹` or similar. Since the unit is `δ(s)^n ≠ 0`,
`f x * unit⁻¹ = 0 ⟹ f x = 0`. Pin the exact lemma (`IsLocalization.lift_mk'`,
`IsLocalization.lift_mk'_spec`, `IsLocalization.mk'_eq_zero_iff`?) and the cleanest way to conclude
`evalP x = 0` from `evalAway (mk' x _) = 0`.

Q4. Is there a SIMPLER overall route? E.g. instead of `mk'`-surjectivity + the case split, can I
directly show `chartPsiAeval p = 0` via `IsLocalization.eq_zero_of_fst_eq_zero` or by exhibiting that
`chartPsiAeval p` lies in the image of a known-zero element? Or is the surj + zero-test + seam-B the
canonical route? I want the route with the fewest Mathlib-absent steps at v4.29.

Please answer Q1-Q4 concretely with v4.29 lemma names where you can, and give the cleanest skeleton.

warning: Model metadata for `gpt-5-codex` not found. Defaulting to fallback metadata; this can degrade performance and cause issues.
codex
**Q1 Soundness**
- The split on `δ(s) := eval s detSchurS` is valid: `δ(s)=0` forces `eval s (map (evalFibrePt hy) (gF * x)) = 0` because the `map` respects products and `map … gF = detSchurS`. The only nontrivial branch is `δ(s) ≠ 0`, where the localized evaluation exists. So a single factor of `gF` is sufficient, and applying `away_mk'_eq_zero_iff_exists_pow_mul_eq_zero` with `m = 1` closes the zero test once you show `evalP s B x = 0`. No extra power is needed because the seam hypothesis already covers all `s` and `y`.  

**Q2 Matching the two coefficient evaluations**
- Use `MvPolynomial.aeval_eq_eval₂` together with `MvPolynomial.eval₂_map` (or the bundled form `MvPolynomial.eval₂_at`). Both `evalF B` and `evalFibrePt hy` are `O(F)`-algebra maps into `k`, each built as `AlgHom.comp` of the same lift `MvPolynomial.eval₂AlgHom`. Once you transport along the witness `hy : canonicalCoord B ∈ F`, the constructions become definitional; concretely you can rewrite with
  - `evalF_eq_liftAeval` (the built lemma that exposes `evalF` as `algebraMap` + `aeval`),
  - `evalFibrePt_eq_liftAeval`, and then finish with `rfl` after coercions.  
  This gives `evalP s B = (MvPolynomial.aevalTower _ s)` and `eval s (map (evalFibrePt hy) ·)` as the same composite map.

**Q3 Extracting `evalP x = 0` from the localized zero**
- Write `chartPsiAeval p = IsLocalization.mk' _ x ⟨_,⟩`. Evaluating with `evalAway` gives
  ```
  have hx := congrArg (evalAway s B hs) hzero
  simp [IsLocalization.lift_mk', evalAway_algebraMap, evalP_gF, IsLocalization.algHom_mk'] at hx
  ```
  In Mathlib v4.29 the key lemmas are `IsLocalization.lift_mk'`, `IsLocalization.lift_mk'_spec`, and `IsLocalization.eq_zero_of_fst_eq_zero`. They identify
  ```
  evalAway s B hs (IsLocalization.mk' _ x ⟨gF^n, _⟩)
      = evalP s B x * (algebraMap _ _ (δ(s)^n))⁻¹
  ```
  Because `hs` says `δ(s)` is a unit, `mul_left_cancel₀` (or directly `IsUnit.mul_left_cancel`) yields `evalP s B x = 0`. The combo `IsLocalization.mk'_eq_zero_iff_exists_pow_mul_eq_zero` you already have then promotes the pointwise zero to the global `gF * x = 0`.

**Q4 Alternative routes**
- A shorter route is to apply `IsLocalization.map_eq_zero_of_mem` to show that the image of `p` lands in the kernel once you exhibit `gF * chartPsiAeval p = 0`. This is essentially the same argument but phrased at the level of the localization map rather than choosing representatives. In Mathlib v4.29 there is no more direct lemma for ideals over localizations, so the “surjectivity + zero-test + seam-B” approach is the standard proof-pattern and matches existing API; keeping `mk'` explicit is usually the least resistance.
- You could also recast the goal as `map (chartPsiAeval.toAlgHom) (vanishingIdeal Σ) ≤ ⊥` and use `Ideal.map_eq_bot_iff_le_comap`; this only shifts the localization step and still depends on the same power-of-`gF` annihilation, so it is not materially shorter.
tokens used
18,895
**Q1 Soundness**
- The split on `δ(s) := eval s detSchurS` is valid: `δ(s)=0` forces `eval s (map (evalFibrePt hy) (gF * x)) = 0` because the `map` respects products and `map … gF = detSchurS`. The only nontrivial branch is `δ(s) ≠ 0`, where the localized evaluation exists. So a single factor of `gF` is sufficient, and applying `away_mk'_eq_zero_iff_exists_pow_mul_eq_zero` with `m = 1` closes the zero test once you show `evalP s B x = 0`. No extra power is needed because the seam hypothesis already covers all `s` and `y`.  

**Q2 Matching the two coefficient evaluations**
- Use `MvPolynomial.aeval_eq_eval₂` together with `MvPolynomial.eval₂_map` (or the bundled form `MvPolynomial.eval₂_at`). Both `evalF B` and `evalFibrePt hy` are `O(F)`-algebra maps into `k`, each built as `AlgHom.comp` of the same lift `MvPolynomial.eval₂AlgHom`. Once you transport along the witness `hy : canonicalCoord B ∈ F`, the constructions become definitional; concretely you can rewrite with
  - `evalF_eq_liftAeval` (the built lemma that exposes `evalF` as `algebraMap` + `aeval`),
  - `evalFibrePt_eq_liftAeval`, and then finish with `rfl` after coercions.  
  This gives `evalP s B = (MvPolynomial.aevalTower _ s)` and `eval s (map (evalFibrePt hy) ·)` as the same composite map.

**Q3 Extracting `evalP x = 0` from the localized zero**
- Write `chartPsiAeval p = IsLocalization.mk' _ x ⟨_,⟩`. Evaluating with `evalAway` gives
  ```
  have hx := congrArg (evalAway s B hs) hzero
  simp [IsLocalization.lift_mk', evalAway_algebraMap, evalP_gF, IsLocalization.algHom_mk'] at hx
  ```
  In Mathlib v4.29 the key lemmas are `IsLocalization.lift_mk'`, `IsLocalization.lift_mk'_spec`, and `IsLocalization.eq_zero_of_fst_eq_zero`. They identify
  ```
  evalAway s B hs (IsLocalization.mk' _ x ⟨gF^n, _⟩)
      = evalP s B x * (algebraMap _ _ (δ(s)^n))⁻¹
  ```
  Because `hs` says `δ(s)` is a unit, `mul_left_cancel₀` (or directly `IsUnit.mul_left_cancel`) yields `evalP s B x = 0`. The combo `IsLocalization.mk'_eq_zero_iff_exists_pow_mul_eq_zero` you already have then promotes the pointwise zero to the global `gF * x = 0`.

**Q4 Alternative routes**
- A shorter route is to apply `IsLocalization.map_eq_zero_of_mem` to show that the image of `p` lands in the kernel once you exhibit `gF * chartPsiAeval p = 0`. This is essentially the same argument but phrased at the level of the localization map rather than choosing representatives. In Mathlib v4.29 there is no more direct lemma for ideals over localizations, so the “surjectivity + zero-test + seam-B” approach is the standard proof-pattern and matches existing API; keeping `mk'` explicit is usually the least resistance.
- You could also recast the goal as `map (chartPsiAeval.toAlgHom) (vanishingIdeal Σ) ≤ ⊥` and use `Ideal.map_eq_bot_iff_le_comap`; this only shifts the localization step and still depends on the same power-of-`gF` annihilation, so it is not materially shorter.
