**1. VERDICT:** Route **3** is the cleanest complete descent: keep the point-realization argument, but use Route **1**’s target-side `IsLocalization.mk'_eq_zero_iff` on `P := MvPolynomial SchurVar OF`. Do **not** try to reuse the Σ-side primitive.

**2. MECHANISM**
For `p ∈ vanishingIdeal k Σ`, prove `chartPsiAeval p = 0` as follows.

1. Set `P := MvPolynomial SchurVar OF`, `T := Localization.Away gF`.
2. Choose a numerator presentation using verified API:
   `IsLocalization.exists_mk'_eq (M := Submonoid.powers gF) (S := T)`:
   ```lean
   chartPsiAeval p = IsLocalization.mk' T num den
   ```
   with `den = ⟨gF^N, N, rfl⟩`.
3. For each `s : SchurVar → k` and `B ∈ F`, define
   `evP s B : P →ₐ[k] k` by evaluating coefficients `OF →ₐ[k] k` via
   `Ideal.Quotient.liftₐ (vanishingIdeal k F) (MvPolynomial.eval (canonicalCoord d B)) ...`,
   then evaluating Schur variables at `s`.
4. If `evP s B gF ≠ 0`, lift this to
   `evLoc s B : T →ₐ[k] k` using verified `IsLocalization.liftAlgHom`.
5. Prove the semantic realization lemma:
   ```lean
   evLoc s B (chartPsiAeval p) =
     MvPolynomial.eval (canonicalCoord d A) p
   ```
   where `A := chartGauge(M)⁻¹ • B`, and your point-realization gives `canonicalCoord d A ∈ Σ`.
6. Since `p ∈ vanishingIdeal k Σ`, the RHS is `0`.
7. From `mk'_spec`, on `D(gF)` get `evP s B num = 0`. Off `D(gF)`, `evP s B (gF * num) = 0` trivially. Hence:
   ```lean
   ∀ s B ∈ F, evP s B (gF * num) = 0
   ```
8. Use the product-quotient zero lemma:
   ```lean
   (∀ s B ∈ F, evP s B h = 0) → h = 0
   ```
   with `h := gF * num`.
9. Apply verified `IsLocalization.mk'_eq_zero_iff`; choose the killer `⟨gF, 1, rfl⟩ : Submonoid.powers gF`.

Then `Ideal.Quotient.liftₐ` gives `OΣ →ₐ[k] T`, and `IsLocalization.liftAlgHom` localizes the source once you prove the image of `dsig` is a unit.

**3. THE gF-SIDE ZERO-TEST**
Yes: `IsLocalization.mk'_eq_zero_iff` on `P` is enough. The general lemma you want is:

```lean
lemma away_mk'_eq_zero_iff_exists_pow_mul_eq_zero
    {R S} [CommSemiring R] [CommSemiring S] [Algebra R S]
    {g : R} [IsLocalization.Away g S]
    (x : R) (d : Submonoid.powers g) :
    IsLocalization.mk' S x d = 0 ↔ ∃ n : ℕ, g^n * x = 0
```

Proof: `rw [IsLocalization.mk'_eq_zero_iff]`, then unwrap `Submonoid.powers`.

For `P = MvPolynomial SchurVar OF`, the equality
```lean
gF^n * x = 0
```
reduces coefficientwise:
```lean
∀ m, (gF^n * x).coeff m = 0 in OF
```
then, after choosing representatives in `MvPolynomial (RepCoord d) k`,
```lean
representative ∈ vanishingIdeal k F
```
by verified `Ideal.Quotient.eq_zero_iff_mem`. If using a global lift, use verified
`MvPolynomial.quotientEquivQuotientMvPolynomial` and `MvPolynomial.mem_map_C_iff`.

**4. RANK-EXACTLY-r CATCH**
The symbolic route (2) only suffices if you already have a theorem like:
```lean
vanishingIdeal k (canonicalCoord '' productRankLocus d r)
  = (Ideal.span {pulled back (r+1)-minors of Matrix.of (multPoly d)}).radical
```
or the equivalent closed rank-`≤ r` presentation plus density of exact rank inside rank-`≤ r`.

Without that theorem, `chartPsiAeval (multPoly _ _ _) = constant E _ _` only kills the obvious defining generators. It does not by itself kill an arbitrary `p ∈ vanishingIdeal Σ`. So for the full radical vanishing ideal, the point-realization route is the practical one.

**5. THE WALL**
The likely wall is this custom bridge:
```lean
lemma eq_zero_of_forall_eval_schur_fibre
    (h : MvPolynomial SchurVar OF)
    (hh : ∀ s B, B ∈ F → evP s B h = 0) :
    h = 0
```

Mitigation: prove it coefficientwise. For fixed `B`, use `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical` with `⊥` to show a Schur polynomial vanishing at all `s` is zero. Then use `MvPolynomial.coeff_map` and `Ideal.Quotient.eq_zero_iff_mem` to put each coefficient in `vanishingIdeal k F`.

**6. NEEDS-VERIFICATION**
Verified in local Mathlib v4.29: `IsLocalization.mk'_eq_zero_iff`, `IsLocalization.exists_mk'_eq`, `IsLocalization.mk'_spec`, `IsLocalization.liftAlgHom`, `Ideal.Quotient.liftₐ`, `Ideal.Quotient.eq_zero_iff_mem`, `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`, `MvPolynomial.zeroLocus_bot`, `MvPolynomial.coeff_map`, `MvPolynomial.mem_map_C_iff`, `MvPolynomial.quotientEquivQuotientMvPolynomial`.

NEEDS-VERIFICATION if you use them by exact name: field unit simp names for `evP s B gF ≠ 0 → IsUnit ...`, and any ready-made reduced-localization instance for `Localization.Away`.