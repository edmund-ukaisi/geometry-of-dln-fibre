# Codex consult — Lean route for the catenary ≥ direction (L5.7 equality)

Lean 4 + Mathlib v4.29.0. Goal: prove, for `R = MvPolynomial (Fin n) k`, `[Field k]`, `p` prime:
`Ideal.height p + ringKrullDim (R ⧸ p) = (n : WithBot ℕ∞)`.

The `≤` direction is landed (`primeHeight_add_ringKrullDim_quotient_le`). Need the `≥` direction
`height p ≥ n − dim(R/p)`, by induction on `n` peeling one variable.

## Bricks ALREADY PROVED (Core engine, available):
- `ringKrullDim_mvPolynomial_fin_field k n : ringKrullDim (MvPolynomial (Fin n) k) = (n:WithBot ℕ∞)`
- `ringKrullDim_eq_of_integral_injective {f : A →+* S} (hf : f.IsIntegral) (hinj : Injective f) : ringKrullDim S = ringKrullDim A`  (L5.4)
- `ringKrullDim_quotient_eq_coheight (p : PrimeSpectrum R) : ringKrullDim (R ⧸ p.asIdeal) = (coheight p : WithBot ℕ∞)`
- `height_eq_height_under_add_height_map_quotient {A} [CommRing A][IsNoetherianRing A] (P : Ideal A[X]) [P.IsPrime] : P.height = (P.under A).height + (P.map (Quotient.mk ((P.under A).map (algebraMap A A[X])))).height`  (additive brick on the 1-var tower, unconditional via flat going-down)

## Mathlib private machinery I can copy/expose (NoetherNormalization.lean):
`T f : MvPolynomial (Fin (n+1)) k ≃ₐ[k] MvPolynomial (Fin (n+1)) k` (substitution X_i ↦ X_i + X_0^(up^i) for i≠0, X_0↦X_0, up = 2+f.totalDegree), and `T_leadingcoeff_isUnit (fne : f ≠ 0) : IsUnit (finSuccEquiv k n (T f f)).leadingCoeff`. These are `private`. The whole `equivT` section (lt_up, sum_r_mul_ne, degreeOf_zero_t, degreeOf_t_ne_of_ne, leadingCoeff_finSuccEquiv_t, T_leadingcoeff_isUnit) is ~100 lines.

`finSuccEquiv k n : MvPolynomial (Fin (n+1)) k ≃ₐ[k] (MvPolynomial (Fin n) k)[X]` isolates X_0.

## Key Mathlib lemmas:
- `Polynomial.Monic.quotient_isIntegral {g : S[X]} (mon : g.Monic) {I : Ideal S[X]} (h : g ∈ I) : ((Ideal.Quotient.mkₐ S I).comp (Algebra.ofId S S[X])).IsIntegral`
- `isIntegral_quotientMap_iff {I : Ideal S} : (Ideal.quotientMap I f le_rfl).IsIntegral ↔ ((Quotient.mk I).comp f).IsIntegral`
- `Ideal.quotientMap_injective`
- `RingEquiv.height_map (e : R ≃+* S) (I : Ideal R) : (I.map e).height = I.height`  (also height_comap)
- `monic_of_isUnit_leadingCoeff_inv_smul (h : IsUnit p.leadingCoeff) : (p.leadingCoeff⁻¹ • p).Monic`
- `Ideal.height_eq_primeHeight [I.IsPrime]`, `Ideal.primeHeight_add_one_le_of_lt`

## Questions

1. **Monic-positioning packaging.** I plan to copy the `equivT` section to get `T f` + unit leading coeff. The cleanest *public* statement to expose for the induction: is it
   (a) `∃ φ : MvPolynomial (Fin (n+1)) k ≃ₐ[k] MvPolynomial (Fin (n+1)) k, IsUnit (finSuccEquiv k n (φ f)).leadingCoeff`, or
   (b) something stated directly about the ideal `p` containing a *monic* element after applying `φ` then `finSuccEquiv`?
   I want to feed it into the additive brick which lives over `A = MvPolynomial (Fin n) k`, `S = A[X]`, and needs the *ideal* `P := (p.map φ).map finSuccEquiv` (an ideal of `A[X]`) to contain a monic poly. What's the least-friction bridge from `IsUnit leadingCoeff` of an *element* to a *monic element of the mapped ideal*?

2. **Dimension preservation.** I want `ringKrullDim (A[X] ⧸ P) = ringKrullDim (A ⧸ P.under A)` when `P` prime contains a monic poly. Route: `Monic.quotient_isIntegral` gives `A → A[X]/P` integral; then `isIntegral_quotientMap_iff` + `quotientMap_injective` to get `A/(P.under A) → A[X]/P` integral injective, then L5.4. Is `isIntegral_quotientMap_iff` the right bridge, and does `Ideal.quotientMap P (algebraMap A A[X]) le_rfl` defeq the map I need? Watch: `P.under A = P.comap (algebraMap A A[X])` (`under_def`). Any traps with the `mkₐ.comp (Algebra.ofId)` vs `(Quotient.mk).comp (algebraMap)` forms?

3. **The induction invariant.** Codex (prior thread) suggested inducting on `m` with invariant `∀ p prime, ∀ s ≤ m, dim(R/p) = s → (m - s : ℕ∞) ≤ p.height`. But `dim(R/p)` is `WithBot ℕ∞` and `height` is `ℕ∞`; subtraction in `ℕ∞` truncates. Is it cleaner to state the invariant as `(n : ℕ∞) ≤ p.height + dim(R/p)` (no subtraction, with dim coerced to ℕ∞ — but dim is WithBot ℕ∞)? What's the cleanest target type to avoid WithBot/ℕ∞/ℕ coercion hell? Note dim(R/p) is finite (= coheight, ≤ n) so it's `(c : ℕ)` for some c; the equality I ultimately want is in `WithBot ℕ∞`.

4. **Transfer across φ.** After proving the bound for `P = (p.map φ).map finSuccEquiv` over `A[X]`, I transfer back: `p.height = ((p.map φ)).height` (φ algebra equiv, `RingEquiv.height_map`) `= P.height` (finSuccEquiv, height_map). And `dim(R/p) = dim(R/(p.map φ))` (quotientEquivAlg + ringKrullDim_eq_of_ringEquiv) `= dim(A[X]/P)`. Confirm both transfers are clean and `[P.IsPrime]` propagates (image of prime under an equiv is prime).

Give me: the cleanest decomposition into named lemmas, the exact target type for the induction invariant, and any v4.29 traps in the coercion / `under` / `quotientMap` plumbing. Rank routes; flag any step that's secretly hard.
