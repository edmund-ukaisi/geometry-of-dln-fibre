**Route**

Take **(c): standard-smooth locally, then étale over affine space**.

Do not use route (a) unless forced. The quotient-presentation route asks you to prove the Jacobian relations form a regular sequence/complete intersection at the point. Mathlib has the dimension drop once a regular sequence exists, but not the bridge from “Jacobian minor is a unit” to “relations are regular”. That is the balloon.

Concrete route:

1. From smoothness at `m`, use verified
   `IsSmoothAt.exists_notMem_isStandardSmooth`
   to get `f ∉ m` and
   `S := Localization.Away f` with `Algebra.IsStandardSmooth k S`.

2. Let `q := m.map (algebraMap A S)`. Since `f ∉ m`, `q` is prime/maximal and `(S)_q ≃ A_m`.
   Use localization APIs such as verified:
   `IsLocalization.isPrime_of_isPrime_disjoint`,
   `IsLocalization.comap_map_of_isPrime_disjoint`,
   `Localization.localizationLocalizationAtPrimeIsoLocalization`,
   `ringKrullDim_eq_of_ringEquiv`.

3. Choose a submersive presentation of `S` and set `n := P.dimension`. Then install
   `Algebra.IsStandardSmoothOfRelativeDimension n k S`.

   Verified decls:
   `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`
   gives
   `Module.rank S Ω[S⁄k] = n`.

4. Use verified
   `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`
   to get an étale map
   `g : MvPolynomial (Fin n) k →ₐ[k] S`.

5. Let `p := q.under (MvPolynomial (Fin n) k)`. Show `p` is maximal. This is not automatic from étale alone; use a small Jacobson finite-type lemma:
   if `R` is Jacobson and `S` is finite type over `R`, then the contraction of a maximal ideal of `S` is maximal. `MvPolynomial (Fin n) k` is Jacobson.

6. Polynomial closed-point dimension:
   from the repo’s polynomial dimension theorem
   `height_add_ringKrullDim_quotient_eq k n p`
   and `p.IsMaximal`, get
   `(p.height : WithBot ℕ∞) = n`.

7. Use the new height-preservation lemma for étale/quasi-finite flat maps:
   `q.height = p.height`.

8. Then
   `ringKrullDim (Localization.AtPrime q) = q.height`
   by verified
   `IsLocalization.AtPrime.ringKrullDim_eq_height`,
   hence
   `ringKrullDim (Localization.AtPrime q) = n`,
   and transport across `(S)_q ≃ A_m`.

So the independent bridge is:

```lean
ringKrullDim (Localization.AtPrime m) = (n : WithBot ℕ∞)
```

where the same `n` is obtained from the standard-smooth relative dimension/rank of `Ω`.

**Load-Bearing Absent Lemma**

The real missing lemma is:

```lean
theorem Ideal.height_eq_under_of_flat_quasiFiniteAt
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing S] [Module.Flat R S]
    {Q : Ideal S} [Q.IsPrime] [Algebra.QuasiFiniteAt R Q] :
    Q.height = (Q.under R).height
```

This is bounded. Proof uses verified existing Mathlib:

- `Algebra.HasGoingDown.of_flat`
- `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`
- `Algebra.QuasiFiniteAt.eq_of_le_of_under_eq`
- `Ideal.primeHeight_eq_zero_iff`
- quotient ideal map/comap lemmas

Sketch: the going-down height formula gives

```lean
Q.height =
  (Q.under R).height +
  (Q.map (Ideal.Quotient.mk ((Q.under R).map (algebraMap R S)))).height
```

The second summand is zero because any lower prime in the fibre quotient pulls back to a prime
`Q' ≤ Q` with the same contraction to `R`; quasi-finite-at forces `Q' = Q`.

Then add the étale corollary:

```lean
theorem Ideal.height_eq_under_of_etale
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing S] [Algebra.Etale R S]
    {Q : Ideal S} [Q.IsPrime] :
    Q.height = (Q.under R).height
```

using `RingHom.Etale.iff_flat_and_formallyUnramified` plus the verified instance
`[EssFiniteType R S] [FormallyUnramified R S] : Algebra.QuasiFinite R S`.

Route (a)’s “height of relation ideal = number of relations” is not just one lemma in practice. Krull height gives `≤`; Mathlib’s regular-sequence dimension-drop closes the problem only after you already have the regular sequence. The missing Jacobian-minor-to-regular-sequence bridge is a real complete-intersection sublibrary.

**Size Verdict**

L4a is now a **bounded build**, not a multi-week library, if you take route (c).

I would budget about **3 small modules**:

1. `FlatQuasiFiniteHeight`: prove `height_eq_under_of_flat_quasiFiniteAt` and the étale corollary.
2. `JacobsonClosedPoint`: contraction of maximal ideals under finite-type maps from Jacobson rings.
3. `SmoothLocalDimension`: assemble standard-smooth → étale affine space → local dimension/rank transport.

Hardest lemmas:

- `Ideal.height_eq_under_of_flat_quasiFiniteAt`
- localization glue `(A_f)_q ≃ A_m` plus rank transport for `Ω`

Kill-condition: if the height-preservation lemma fails to assemble from the existing quasi-finite specialization uniqueness API, the task balloons into a fibre-dimension/dimension-formula library. I do not think that happens; the existing `QuasiFiniteAt.eq_of_le_of_under_eq` is exactly the missing zero-dimensional fibre input.

**Traps**

- `A` need not be a domain. Route (a) quietly wants a component/domain reduction; route (c) does not.
- `IsSmoothAt.exists_notMem_isStandardSmooth` needs finite presentation. For finite type over a field, use `Algebra.FinitePresentation.of_finiteType` with the field Noetherian instance.
- Do not compute `ringKrullDim A_f`; compute `ringKrullDim (Localization.AtPrime q)`.
- The `n` from `exists_etale_mvPolynomial` must be tied to the same standard-smooth relative dimension used for `Module.rank Ω = n`.
- Rank transport for `Ω` goes through `KaehlerDifferential.isLocalizedModule_map` and `Module.lift_rank_of_isLocalizedModule_of_free`; expect `Cardinal.lift` bookkeeping.
- Use `IsRegularLocalRing.iff_finrank_cotangentSpace` only after the independent equality `ringKrullDim A_m = n` is proved.