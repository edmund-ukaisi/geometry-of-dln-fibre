**1. VERDICT:** Use route **3**: point-realization plus a new target-side principal-open zero lemma for `P[1/gF]`; route 1 is the zero-test inside it, and route 2 is not enough.

**2. MECHANISM:** Prove
`vanishingIdeal k Σ ≤ RingHom.ker chartPsiAeval.toRingHom` as follows.

1. For `B ∈ F`, define
   `evalF B hB : OF →ₐ[k] k`
   by `Ideal.Quotient.liftₐ` from `MvPolynomial.aeval B`, using
   `MvPolynomial.mem_vanishingIdeal_iff`.

2. For `s : SchurVar → k`, define
   `evalP s B hB : P →ₐ[k] k`
   using `MvPolynomial.eval₂Hom (evalF B hB).toRingHom s`.

3. If `eval s detSchurS ≠ 0`, lift this to
   `evalAway s B hB hs : Localization.Away gF →ₐ[k] k`
   via `IsLocalization.liftAlgHom` or `IsLocalization.Away.lift`; `evalP s B hB gF` reduces to `eval s detSchurS`.

4. Prove the chart evaluation lemma:
   `evalAway ... (chartPsiAeval p) = aeval (canonicalCoord d A) p`,
   where `A := chartGauge(M(s))⁻¹ • B`. Then point-realization gives `A ∈ Σ`, so `p ∈ vanishingIdeal k Σ` gives zero.

5. Apply the target-side zero lemma from item 3 below to conclude `chartPsiAeval p = 0`.

6. Then use `Ideal.Quotient.liftₐ`; after that localize the source with `IsLocalization.liftAlgHom`, using the already-planned proof that the image of `dsig` is a unit.

**3. THE gF-SIDE ZERO-TEST:** Yes: `IsLocalization.mk'_eq_zero_iff` on `P` is the right localization test. For `S := Localization.Away gF`,
```lean
IsLocalization.mk' S a t = 0
↔ ∃ m : Submonoid.powers gF, (m : P) * a = 0
```
and unpacking `m ∈ powers gF` gives the expected `∃ n, gF^n * a = 0`. This is generic localization API, not a `vanishingIdeal` lemma. ([leanprover-community.github.io](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Localization/Defs.html))

The geometric part should prove a stronger numerator lemma:
```lean
(∀ s B, B ∈ F → eval s detSchurS ≠ 0 → evalP s B hB a = 0)
→ gF * a = 0
```
in `P = MvPolynomial SchurVar OF`. Prove it coefficientwise:
- use `MvPolynomial.ext_iff`;
- show each coefficient is zero in `OF`;
- prove `c = 0` in `OF` by quotient induction and `MvPolynomial.mem_vanishingIdeal_iff`;
- for fixed `B ∈ F`, map coefficients to `k` and use `MvPolynomial.funext` over the Schur variables. `MvPolynomial.funext` is the API for equality from all evaluations over an infinite integral domain, and `[CharZero k]` supplies infinitude. ([leanprover-community.github.io](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/MvPolynomial/Funext.html))

Equivalently, `MvPolynomial.mem_map_C_iff` and `MvPolynomial.quotientEquivQuotientMvPolynomial` are available if you choose to identify `P` with a quotient, but the coefficientwise route is cheaper. ([leanprover-community.github.io](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Polynomial/Basic.html))

**4. RANK-EXACTLY-r CATCH:** The point-realization argument is the pragmatic route. The symbolic route as stated is not correct: Ψ should send `multPoly` to the varying Schur matrix `M(s)`, not to the constant normal form `E`; the constant `E` is the product after normalization/on the fibre side.

To make a purely symbolic route work, you would need a proved description of the full `vanishingIdeal k Σ`, e.g. equality with the closure/rank-`≤ r` determinantal ideal or its radical generators. That is a substantial extra theorem; `sigmaIdeal` being a `vanishingIdeal` is not a finite generator presentation.

**5. THE WALL:** The real wall is the new target lemma:
```lean
gF_mul_eq_zero_of_eval_vanish_on_principalOpen
```
or the packaged version
```lean
away_gF_eq_zero_of_forall_evalAway_eq_zero
```
for `P = MvPolynomial SchurVar OF`.

Mitigation: do not use a product-variety Nullstellensatz. Prove it by coefficients in `SchurVar`, then by quotient induction in `OF`, with `MvPolynomial.funext` only over `k`.

**6. NEEDS-VERIFICATION:** No Mathlib names above are inferred; they were checked against the local v4.29 tree. Proposed lemma names such as `gF_mul_eq_zero_of_eval_vanish_on_principalOpen` are new DLNFibre lemmas, not Mathlib API.