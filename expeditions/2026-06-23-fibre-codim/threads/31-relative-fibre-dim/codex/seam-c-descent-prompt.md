# Consult: Lean 4 / Mathlib v4.29 — assemble a vanishingIdeal-descent into a localization

I am formalising in Lean 4 + Mathlib v4.29. I have a chart-evaluation lemma and a coefficientwise
zero-test already PROVED, and I need to assemble them into a vanishingIdeal-descent obligation. I want
you to (a) confirm the logical assembly is sound, (b) pin the exact Mathlib API names I'll need, and
(c) flag any subtlety I'm missing.

## The objects (all LANDED, sorry-free, in my library)

- `k` : an algebraically closed field of char 0 (so `Infinite k`).
- `P := MvPolynomial SchurVar (O(F))`, where `O(F) = MvPolynomial τ k ⧸ vanishingIdeal F`
  (a poly ring over the fibre coordinate ring; F ⊆ (τ → k) is the fibre).
- `gF : P` the localizing element. CRUCIAL: `gF = MvPolynomial.map (algebraMap k O(F)) detSchurS`
  where `detSchurS : MvPolynomial SchurVar k`. So `gF` has `k`-coefficients lifted to O(F).
- `Away gF := Localization.Away gF`, an `O(F)`- and `k`-algebra.
- `chartPsiAeval : MvPolynomial (RepCoord d) k →ₐ[k] Away gF` (the comorphism; un-descended).
- `vanishingIdeal Σ : Ideal (MvPolynomial (RepCoord d) k)` for a set `Σ ⊆ (RepCoord d → k)` =
  `canonicalCoord '' productRankLocus`.

## Chart-eval lemma (I am about to prove this; route is de-risked):

For every `s : SchurVar → k` and `B ∈ fibre E` with `hs : eval s detSchurS ≠ 0`, there is a
`k`-algebra hom `evalAway s B hs : Away gF →ₐ[k] k` (the localized chart-point evaluation), and:

  `chartEvalLemma : evalAway s B hs (chartPsiAeval p) = aeval (canonicalCoord A) p`

where `A := baseChange (evalGauge (schurEval s) endpointGauge⁻¹) B : Tuple d` and, by the
homogeneous-sweep realization (`mem_productRankLocus_iff_mem_sweep`), `A ∈ productRankLocus d r`,
hence `canonicalCoord A ∈ Σ`. So for `p ∈ vanishingIdeal Σ`: `aeval (canonicalCoord A) p =
eval (canonicalCoord A) p = 0`. Therefore:

  `(*)  ∀ s B (hs : eval s detSchurS ≠ 0), evalAway s B hs (chartPsiAeval p) = 0`.

Also I have:
- `evalAway_algebraMap : evalAway s B hs (algebraMap P (Away gF) a) = evalP s B a`, where
  `evalP s B : P →ₐ[k] k = aevalTower (evalF B) s` (evaluate O(F)-coeffs at B, SchurVar-vars at s).
- `evalP_gF : evalP s B gF = eval s detSchurS`.

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
