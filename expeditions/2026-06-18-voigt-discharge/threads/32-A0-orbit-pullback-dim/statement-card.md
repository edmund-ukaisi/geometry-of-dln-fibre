# A0 — route-c setup: `varietyDim(Z_M) = ringKrullDim((μ_M^*).range)`

The first link of the L2b★ route-c chain (`varietyDim(Z_M) = ringKrullDim(image μ_M^*) = trdeg(image)
≤ finrank(range δ⁰)`) that discharges `hVoigt` on the AG half. The variety dimension of the
determinantal rank locus `Z_M = canonicalCoord '' orbitRankLocus M` is identified with the Krull
dimension of the image of the orbit-map pullback `μ_M^*`, a finitely-generated **domain**. Module:
`lean/DLNFibre/Core/OrbitPullbackDim.lean`. Over an **infinite** field — no algebraic closure (the
fidelity review flagged the earlier `[IsAlgClosed k]` as inherited from an over-strong brick
signature; the brick `vanishingIdeal_range_orbitMap_eq_ker` was weakened to `[Infinite k]`).

**Fidelity-reviewed** (independent + Codex-corroborated): SURVIVED — statement matches the claimed
route-c first link, `[Infinite k]` is the honest weakest hypothesis, no overclaim. Verified against
fresh oleans (an earlier `[IsAlgClosed k]` signature reading was a stale-olean artifact in the
reviewer's tooling, not a defect).

---

> **Claim (A0 headline).** For a composable matrix tuple `M : Tuple d` over an **infinite** field, the
> variety dimension of the flattened determinantal rank locus `canonicalCoord '' orbitRankLocus M`
> equals the Krull dimension of the image of the orbit-map pullback `(orbitPullback M).range`, which
> is a domain.
>
> - **Lean:** `DLNFibre.Core.varietyDim_eq_ringKrullDim_range_orbitPullback`
>   (`lean/DLNFibre/Core/OrbitPullbackDim.lean` @ `c854f5f`)
> - **Gloss.** `[Field k] [Infinite k]`; `M : Tuple d`. Then
>   `varietyDim (canonicalCoord d '' orbitRankLocus M)
>     = (ringKrullDim (orbitPullback M).range).unbotD 0` in `ℕ∞`, where `varietyDim Z =
>   (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal k Z)).unbotD 0` and
>   `orbitPullback M : MvPolynomial (RepCoord d) k →ₐ[k] groupRing d` is the orbit-map pullback
>   (`X ⟨i,r,c⟩ ↦ (r,c) entry of Pgen_{i+1} · M_i · Pgen_i⁻¹` in `𝒪(G_d) = groupRing d`).
> - **Proved.** The dimension equality, unconditionally over any infinite field. Two
>   moves: (i) `varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker` rewrites the coordinate ring's
>   vanishing ideal to `ker μ_M^*` via the `varietyDim` definition, L6.4
>   (`vanishingIdeal_orbitRankLocus_eq_orbitSet`), and the orbit↔kernel identity (`range_orbitMap` +
>   `vanishingIdeal_range_orbitMap_eq_ker`); (ii) the first isomorphism theorem
>   `quotientKerEquivRangeOrbitPullback` (`Ideal.quotientKerEquivRange (orbitPullback M)`) gives
>   `(MvPolynomial (RepCoord d) k ⧸ ker μ_M^*) ≃ₐ[k] (μ_M^*).range`, transported through
>   `ringKrullDim_eq_of_ringEquiv` on the underlying `RingEquiv`.
> - **Assumed.** `[Infinite k]` only. The orbit↔kernel `⊆` rests on `MvPolynomial.funext`, whose
>   Mathlib hypothesis is "infinite integral domain" (`[CommRing] [IsDomain] [Infinite]`) — not
>   algebraic closure; L6.4 also needs only `[Infinite k]`. (The fidelity review demonstrated the whole
>   headline compiles under `[Infinite k]`; the over-strong `[IsAlgClosed k]` was inherited purely from
>   the *as-stated* signature of `vanishingIdeal_range_orbitMap_eq_ker`, since corrected.)
> - **Cited.** none — L6.4 (Abeasis–Del Fra) and L1 (`vanishingIdeal_range_orbitMap_eq_ker`,
>   `groupRing_isDomain`) are proved in-repo and consumed here as lemmas; `Ideal.quotientKerEquivRange`
>   and `ringKrullDim_eq_of_ringEquiv` are Mathlib.
> - **Deferred.** the *value* of `ringKrullDim (μ_M^*).range` as a transcendence degree — A4's job
>   (this card asserts only the dimension *identification*, hands A4 the f.g. domain).
> - **Status.** sorry-free + reviewed

---

> **Claim (A0 helper, ideal form).** `varietyDim (canonicalCoord '' orbitRankLocus M)` equals the
> Krull dimension of the coordinate ring `MvPolynomial (RepCoord d) k ⧸ ker μ_M^*`.
>
> - **Lean:** `DLNFibre.Core.varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker`
>   (`lean/DLNFibre/Core/OrbitPullbackDim.lean` @ `c854f5f`)
> - **Gloss.** `[Field k] [Infinite k]`; `M : Tuple d`. Then
>   `varietyDim (canonicalCoord d '' orbitRankLocus M)
>     = (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ RingHom.ker (orbitPullback M).toRingHom)).unbotD 0`.
> - **Proved.** The `varietyDim` def then two ideal rewrites (L6.4, orbit↔kernel). Pure ideal-level
>   identification, no first-iso theorem yet.
> - **Assumed.** `[Infinite k]` only.
> - **Cited.** none.
> - **Deferred.** none.
> - **Status.** sorry-free + reviewed

---

> **Claim (A0 brick, image is a domain).** `(orbitPullback M).range` is a domain.
>
> - **Lean:** `DLNFibre.Core.isDomain_range_orbitPullback`
>   (`lean/DLNFibre/Core/OrbitPullbackDim.lean` @ `c854f5f`) — an `instance`.
> - **Gloss.** `[Field k]`; `M : Tuple d`. Then `IsDomain (orbitPullback M).range`. The range is a
>   subalgebra of the domain `𝒪(G_d) = groupRing d` (`groupRing_isDomain` from `OrbitVariety`), and a
>   subring of a domain is a domain (Mathlib `Subring`/`SubringClass` instance) — fires by
>   `inferInstance`. Char-free: no `Infinite`/`IsAlgClosed` needed.
> - **Proved.** The domain instance, unconditionally over any field.
> - **Assumed.** none beyond `[Field k]`.
> - **Cited.** none.
> - **Deferred.** none.
> - **Status.** sorry-free + reviewed

---

## Non-vacuity

The headline holds over any infinite field, so it applies directly to the `(2,2,2)/ℚ` tuple
`tupleWitnessQ` (`ℚ` is infinite) — the dimension *equality* is exhibited concretely, not merely the
objects' inhabitance. Two in-file `example`s: `varietyDim (canonicalCoord dWitness '' orbitRankLocus
tupleWitnessQ) = (ringKrullDim (orbitPullback tupleWitnessQ).range).unbotD 0` (the headline itself at
the ℚ witness) and `IsDomain (orbitPullback tupleWitnessQ).range`.

## Axiom footprint

`#print axioms` on the headline and the ideal-form helper: `[propext, Classical.choice, Quot.sound]`
only — no `sorryAx`, no custom axioms. `scripts/sorries` = 0 across the whole library; `lake build`
green (2696 jobs).

## Hypothesis-weakening note (carried out)

The earlier draft of this card said `[IsAlgClosed k]` was *forced* by the `⊆` localization-vanishing
argument. The fidelity review (independent, Codex-corroborated) showed this is false: the `⊆`
direction uses `MvPolynomial.funext`, which needs only an infinite integral domain, and re-proved the
entire headline under `[Infinite k]`. The brick `vanishingIdeal_range_orbitMap_eq_ker`
(`lean/DLNFibre/Core/OrbitVariety.lean`) was therefore weakened `[IsAlgClosed k] → [Infinite k]`
(proof body unchanged); its downstream `[IsAlgClosed k]` consumer `isPrime_vanishingIdeal_orbitSet`
(which genuinely needs algebraic closure for primeness) is unaffected. A0 now carries the honest
weakest hypothesis `[Infinite k]`.

## Confirmed: `image μ_M^*` is a domain

Yes. `(orbitPullback M).range` is a subalgebra of `groupRing d = Localization.Away (groupDenom d)`,
which is a domain (`groupRing_isDomain`: localization of the polynomial domain `MvPolynomial (GroupCoord
d) k` away from the nonzero `groupDenom d`). The Mathlib `SubringClass`/`Subring` `IsDomain` instance
descends this to the subalgebra. The headline's RHS `ringKrullDim (orbitPullback M).range` is therefore
the Krull dimension of a finitely-generated `k`-domain — the object A4 will compute as a transcendence
degree.
