# A0 — route-c setup: `varietyDim(Z_M) = ringKrullDim((μ_M^*).range)`

The first link of the L2b★ route-c chain (`varietyDim(Z_M) = ringKrullDim(image μ_M^*) = trdeg(image)
≤ finrank(range δ⁰)`) that discharges `hVoigt` on the AG half. The variety dimension of the
determinantal rank locus `Z_M = canonicalCoord '' orbitRankLocus M` is identified with the Krull
dimension of the image of the orbit-map pullback `μ_M^*`, a finitely-generated **domain**. Module:
`lean/DLNFibre/Core/OrbitPullbackDim.lean`.

---

> **Claim (A0 headline).** For a composable matrix tuple `M : Tuple d` over an algebraically closed
> field, the variety dimension of the flattened determinantal rank locus
> `canonicalCoord '' orbitRankLocus M` equals the Krull dimension of the image of the orbit-map
> pullback `(orbitPullback M).range`, which is a domain.
>
> - **Lean:** `DLNFibre.Core.varietyDim_eq_ringKrullDim_range_orbitPullback`
>   (`lean/DLNFibre/Core/OrbitPullbackDim.lean` @ `<this commit>`)
> - **Gloss.** `[Field k] [IsAlgClosed k]`; `M : Tuple d`. Then
>   `varietyDim (canonicalCoord d '' orbitRankLocus M)
>     = (ringKrullDim (orbitPullback M).range).unbotD 0` in `ℕ∞`, where `varietyDim Z =
>   (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal k Z)).unbotD 0` and
>   `orbitPullback M : MvPolynomial (RepCoord d) k →ₐ[k] groupRing d` is the orbit-map pullback
>   (`X ⟨i,r,c⟩ ↦ (r,c) entry of Pgen_{i+1} · M_i · Pgen_i⁻¹` in `𝒪(G_d) = groupRing d`).
> - **Proved.** The dimension equality, unconditionally over any algebraically closed field. Two
>   moves: (i) `varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker` rewrites the coordinate ring's
>   vanishing ideal to `ker μ_M^*` via the `varietyDim` definition, L6.4
>   (`vanishingIdeal_orbitRankLocus_eq_orbitSet`), and the orbit↔kernel identity (`range_orbitMap` +
>   `vanishingIdeal_range_orbitMap_eq_ker`); (ii) the first isomorphism theorem
>   `quotientKerEquivRangeOrbitPullback` (`Ideal.quotientKerEquivRange (orbitPullback M)`) gives
>   `(MvPolynomial (RepCoord d) k ⧸ ker μ_M^*) ≃ₐ[k] (μ_M^*).range`, transported through
>   `ringKrullDim_eq_of_ringEquiv` on the underlying `RingEquiv`.
> - **Assumed.** `[IsAlgClosed k]` (inherited: `vanishingIdeal_range_orbitMap_eq_ker` needs it for the
>   `⊆` localization-vanishing argument; `IsAlgClosed → Infinite` supplies the L6.4 hypothesis).
> - **Cited.** none — L6.4 (Abeasis–Del Fra) and L1 (`vanishingIdeal_range_orbitMap_eq_ker`,
>   `groupRing_isDomain`) are proved in-repo and consumed here as lemmas; `Ideal.quotientKerEquivRange`
>   and `ringKrullDim_eq_of_ringEquiv` are Mathlib.
> - **Deferred.** the *value* of `ringKrullDim (μ_M^*).range` as a transcendence degree — A4's job
>   (this card asserts only the dimension *identification*, hands A4 the f.g. domain).
> - **Status.** sorry-free

---

> **Claim (A0 helper, ideal form).** `varietyDim (canonicalCoord '' orbitRankLocus M)` equals the
> Krull dimension of the coordinate ring `MvPolynomial (RepCoord d) k ⧸ ker μ_M^*`.
>
> - **Lean:** `DLNFibre.Core.varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker`
>   (`lean/DLNFibre/Core/OrbitPullbackDim.lean` @ `<this commit>`)
> - **Gloss.** `[Field k] [IsAlgClosed k]`; `M : Tuple d`. Then
>   `varietyDim (canonicalCoord d '' orbitRankLocus M)
>     = (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ RingHom.ker (orbitPullback M).toRingHom)).unbotD 0`.
> - **Proved.** The `varietyDim` def then two ideal rewrites (L6.4, orbit↔kernel). Pure ideal-level
>   identification, no first-iso theorem yet.
> - **Assumed.** `[IsAlgClosed k]`.
> - **Cited.** none.
> - **Deferred.** none.
> - **Status.** sorry-free

---

> **Claim (A0 brick, image is a domain).** `(orbitPullback M).range` is a domain.
>
> - **Lean:** `DLNFibre.Core.isDomain_range_orbitPullback`
>   (`lean/DLNFibre/Core/OrbitPullbackDim.lean` @ `<this commit>`) — an `instance`.
> - **Gloss.** `[Field k]`; `M : Tuple d`. Then `IsDomain (orbitPullback M).range`. The range is a
>   subalgebra of the domain `𝒪(G_d) = groupRing d` (`groupRing_isDomain` from `OrbitVariety`), and a
>   subring of a domain is a domain (Mathlib `Subring`/`SubringClass` instance) — fires by
>   `inferInstance`. Char-free: no `IsAlgClosed` needed.
> - **Proved.** The domain instance, unconditionally over any field.
> - **Assumed.** none beyond `[Field k]`.
> - **Cited.** none.
> - **Deferred.** none.
> - **Status.** sorry-free

---

## Non-vacuity

The headline carries `[IsAlgClosed k]`, and `ℚ` is not algebraically closed; the chain's objects
(`orbitPullback`, `.range`, the first-iso AlgEquiv) — which do not need algebraic closedness — are
exercised on the `(2,2,2)/ℚ` tuple `tupleWitnessQ` by two in-file `example`s: `IsDomain
(orbitPullback tupleWitnessQ).range` and the first-iso `MvPolynomial (RepCoord dWitness) ℚ ⧸ ker μ_M^*
≃ₐ[ℚ] (μ_M^*).range`.

## Axiom footprint

`#print axioms` on the headline and the ideal-form helper: `[propext, Classical.choice, Quot.sound]`
only — no `sorryAx`, no custom axioms. `scripts/sorries` = 0 across the whole library; `lake build`
green (2696 jobs).

## Confirmed: `image μ_M^*` is a domain

Yes. `(orbitPullback M).range` is a subalgebra of `groupRing d = Localization.Away (groupDenom d)`,
which is a domain (`groupRing_isDomain`: localization of the polynomial domain `MvPolynomial (GroupCoord
d) k` away from the nonzero `groupDenom d`). The Mathlib `SubringClass`/`Subring` `IsDomain` instance
descends this to the subalgebra. The headline's RHS `ringKrullDim (orbitPullback M).range` is therefore
the Krull dimension of a finitely-generated `k`-domain — the object A4 will compute as a transcendence
degree.
