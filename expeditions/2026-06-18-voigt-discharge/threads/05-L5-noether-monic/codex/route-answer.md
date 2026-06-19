   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (fa7351f6ef4773f536ee4975c3251325eb9c44df)
Reading prompt from stdin...
OpenAI Codex v0.141.0
--------
workdir: /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/voigt-discharge
model: gpt-5.1-codex-max
provider: openai-aisi
approval: never
sandbox: read-only
reasoning effort: xhigh
reasoning summaries: none
session id: 019edf0d-5bde-70a2-8ae5-2ea49823f7e5
--------
user
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

warning: Model metadata for `gpt-5.1-codex-max` not found. Defaulting to fallback metadata; this can degrade performance and cause issues.
codex
**Monic Packaging**

- Aim for a lemma: `∃ φ : MvPolynomial (Fin (n+1)) k ≃ₐ[k] MvPolynomial (Fin (n+1)) k, IsUnit (Polynomial.leadingCoeff (finSuccEquiv k n (φ f)))`. This is enough; from `IsUnit lc` get `hmonic : (finSuccEquiv k n (φ f)).leadingCoeff⁻¹ • finSuccEquiv k n (φ f)`.monic via `monic_of_isUnit_leadingCoeff_inv_smul`.  
- Then `hmonic` lies in `(p.map φ).map (finSuccEquiv k n)` provided `f ∈ p`; scaling by a unit keeps membership. The ideal-level bridge:  
  `lemma ideal_has_monic_of_unit_lc {I : Ideal A[X]} {g} (hg : g ∈ I) (h : IsUnit g.leadingCoeff) : ∃ g' ∈ I, g'.Monic := ⟨_, I.smul_mem _ hg, monic_of_isUnit_leadingCoeff_inv_smul h⟩`.

**Dimension Bridge**

- Use `Polynomial.Monic.quotient_isIntegral` to get integrality of `A → A[X]/P` once `P` contains a monic.  
- Convert to the map from `A ⧸ P.under A` via  
  `have h₁ : ((Ideal.Quotient.mkₐ A P).comp (Algebra.ofId A A[X])).IsIntegral := ...`  
  `have h₂ : (Ideal.quotientMap (P.under A) (algebraMap A A[X]) le_rfl).IsIntegral` by `h₁` and `isIntegral_quotientMap_iff`.  
- `Ideal.quotientMap_injective` applies because `algebraMap A A[X]` is injective; hence `ringKrullDim_eq_of_integral_injective h₂ (Ideal.quotientMap_injective _ _ _)` yields `dim (A[X]/P) = dim (A/(P.under A))`.  
- In v4.29, `under_def` rewrites `P.under A` to `Ideal.comap (algebraMap A A[X]) P`; `quotientMap` with `le_rfl` is definitionally the needed map.

**Induction Invariant**

- Use a statement avoiding subtraction: `(n : ℕ∞) ≤ p.height + coe (ringKrullDim (R ⧸ p))`. Since `ringKrullDim (R ⧸ p)` is `WithBot ℕ∞`, coerce to `ℕ∞` via `Option.some`. For primes in `MvPolynomial (Fin n) k`, the dimension is finite, so `ringKrullDim (R ⧸ p) = (d : WithBot ℕ∞)` with `d : ℕ`.  
- Induction on `n` with step: if `P ⊆ A[X]` prime and contains a monic, `P.height ≥ P.under.height + 1`, and `dim(A[X]/P) = dim(A/(P.under A))`, then `(n+1) ≤ P.height + dim(A[X]/P)` follows from the inductive hypothesis applied to `P.under`.

**Transfer Back Across Equivalences**

- Height: `RingEquiv.height_map` gives `(p.map φ).height = p.height`; likewise for `finSuccEquiv`.  
- Primehood: `Ideal.isPrime_iff_isPrime_map` for equivalences; `IsPrime.map` on `Ideal` works directly.  
- Dimension: `ringKrullDim_eq_of_ringEquiv` after transporting the quotient along the induced quotient equivalence `(Quotient.map _ _ ...).trans (Ideal.quotient_equiv _ _)`. So `ringKrullDim (R ⧸ p) = ringKrullDim (R ⧸ p.map φ)` and similarly through `finSuccEquiv`.

**v4.29 Quirks**

- `monic_of_isUnit_leadingCoeff_inv_smul` lives in `Polynomial`; need to `open scoped Polynomial` or qualify.  
- Ensure `finSuccEquiv` target is `(MvPolynomial (Fin n) k)[X]`; coercions to `Polynomial` require `rename`.  
- `coheight` is `WithBot`; `height` is `ℕ∞`. Use `Ideal.height_eq_primeHeight` to jump between them; then `ringKrullDim_quotient_eq_coheight` aligns with `WithBot`.  
- When rewriting `P.under A`, `simp [Ideal.under, Ideal.map]` may unfold unexpectedly; prefer `simp [Ideal.under_def]`.

**Suggested Lemma Names**

- `exists_equiv_with_unit_leadingCoeff (f ≠ 0) : ∃ φ, IsUnit (finSuccEquiv k n (φ f)).leadingCoeff`.  
- `Ideal.monic_in_of_unit_lc (hg : g ∈ I) (h : IsUnit g.leadingCoeff) : ∃ g' ∈ I, g'.Monic`.  
- `ringKrullDim_quot_eq_under_of_monic (P : Ideal A[X]) [P.IsPrime] (hmonic : ∃ g ∈ P, g.Monic) : ringKrullDim (A[X] ⧸ P) = ringKrullDim (A ⧸ P.under A)`.  

These pieces should let the ≥ direction go through with minimal coercion pain.
tokens used
17,226
**Monic Packaging**

- Aim for a lemma: `∃ φ : MvPolynomial (Fin (n+1)) k ≃ₐ[k] MvPolynomial (Fin (n+1)) k, IsUnit (Polynomial.leadingCoeff (finSuccEquiv k n (φ f)))`. This is enough; from `IsUnit lc` get `hmonic : (finSuccEquiv k n (φ f)).leadingCoeff⁻¹ • finSuccEquiv k n (φ f)`.monic via `monic_of_isUnit_leadingCoeff_inv_smul`.  
- Then `hmonic` lies in `(p.map φ).map (finSuccEquiv k n)` provided `f ∈ p`; scaling by a unit keeps membership. The ideal-level bridge:  
  `lemma ideal_has_monic_of_unit_lc {I : Ideal A[X]} {g} (hg : g ∈ I) (h : IsUnit g.leadingCoeff) : ∃ g' ∈ I, g'.Monic := ⟨_, I.smul_mem _ hg, monic_of_isUnit_leadingCoeff_inv_smul h⟩`.

**Dimension Bridge**

- Use `Polynomial.Monic.quotient_isIntegral` to get integrality of `A → A[X]/P` once `P` contains a monic.  
- Convert to the map from `A ⧸ P.under A` via  
  `have h₁ : ((Ideal.Quotient.mkₐ A P).comp (Algebra.ofId A A[X])).IsIntegral := ...`  
  `have h₂ : (Ideal.quotientMap (P.under A) (algebraMap A A[X]) le_rfl).IsIntegral` by `h₁` and `isIntegral_quotientMap_iff`.  
- `Ideal.quotientMap_injective` applies because `algebraMap A A[X]` is injective; hence `ringKrullDim_eq_of_integral_injective h₂ (Ideal.quotientMap_injective _ _ _)` yields `dim (A[X]/P) = dim (A/(P.under A))`.  
- In v4.29, `under_def` rewrites `P.under A` to `Ideal.comap (algebraMap A A[X]) P`; `quotientMap` with `le_rfl` is definitionally the needed map.

**Induction Invariant**

- Use a statement avoiding subtraction: `(n : ℕ∞) ≤ p.height + coe (ringKrullDim (R ⧸ p))`. Since `ringKrullDim (R ⧸ p)` is `WithBot ℕ∞`, coerce to `ℕ∞` via `Option.some`. For primes in `MvPolynomial (Fin n) k`, the dimension is finite, so `ringKrullDim (R ⧸ p) = (d : WithBot ℕ∞)` with `d : ℕ`.  
- Induction on `n` with step: if `P ⊆ A[X]` prime and contains a monic, `P.height ≥ P.under.height + 1`, and `dim(A[X]/P) = dim(A/(P.under A))`, then `(n+1) ≤ P.height + dim(A[X]/P)` follows from the inductive hypothesis applied to `P.under`.

**Transfer Back Across Equivalences**

- Height: `RingEquiv.height_map` gives `(p.map φ).height = p.height`; likewise for `finSuccEquiv`.  
- Primehood: `Ideal.isPrime_iff_isPrime_map` for equivalences; `IsPrime.map` on `Ideal` works directly.  
- Dimension: `ringKrullDim_eq_of_ringEquiv` after transporting the quotient along the induced quotient equivalence `(Quotient.map _ _ ...).trans (Ideal.quotient_equiv _ _)`. So `ringKrullDim (R ⧸ p) = ringKrullDim (R ⧸ p.map φ)` and similarly through `finSuccEquiv`.

**v4.29 Quirks**

- `monic_of_isUnit_leadingCoeff_inv_smul` lives in `Polynomial`; need to `open scoped Polynomial` or qualify.  
- Ensure `finSuccEquiv` target is `(MvPolynomial (Fin n) k)[X]`; coercions to `Polynomial` require `rename`.  
- `coheight` is `WithBot`; `height` is `ℕ∞`. Use `Ideal.height_eq_primeHeight` to jump between them; then `ringKrullDim_quotient_eq_coheight` aligns with `WithBot`.  
- When rewriting `P.under A`, `simp [Ideal.under, Ideal.map]` may unfold unexpectedly; prefer `simp [Ideal.under_def]`.

**Suggested Lemma Names**

- `exists_equiv_with_unit_leadingCoeff (f ≠ 0) : ∃ φ, IsUnit (finSuccEquiv k n (φ f)).leadingCoeff`.  
- `Ideal.monic_in_of_unit_lc (hg : g ∈ I) (h : IsUnit g.leadingCoeff) : ∃ g' ∈ I, g'.Monic`.  
- `ringKrullDim_quot_eq_under_of_monic (P : Ideal A[X]) [P.IsPrime] (hmonic : ∃ g ∈ P, g.Monic) : ringKrullDim (A[X] ⧸ P) = ringKrullDim (A ⧸ P.under A)`.  

These pieces should let the ≥ direction go through with minimal coercion pain.
