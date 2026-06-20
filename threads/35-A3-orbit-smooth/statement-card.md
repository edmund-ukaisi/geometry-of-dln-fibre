# A3 (L3) — smoothness of the orbit closure at the normal-form point: `IsSmoothAt k m_M`

The orbit-closure variety `Z_M = orbitRankLocus M = Ō_M` is **smooth at the orbit normal-form point
`M`**: the coordinate ring `A = MvPolynomial (RepCoord d) k ⧸ vanishingIdeal(orbitSet M)` is formally
smooth over `k` at the maximal ideal `m_M = ker(eval at canonicalCoord M)`. The proof is **homogeneity
+ Route DENSE** (threads 18, 34): the `G_d`-action acts on `Z_M` with a dense orbit, generic smoothness
over the perfect (algebraically closed) field `k` produces a smooth closed point, the dense orbit forces
one such point to be an orbit point, and the `G_d`-action transports its smoothness to the normal-form
point. Module: `lean/DLNFibre/Core/OrbitSmooth.lean`. `[Field k] [IsAlgClosed k]`.

**Consumers:** A6 (assembly) and M3/L2a (cotangent at the `k`-rational point) consume `isSmoothAt_normalFormIdeal`
and `residueFieldNormalFormEquiv` (κ(m_M)=k).

**Fidelity-reviewed** (independent + Codex-corroborated, @ `633766c`): SURVIVED — the Lean statement
faithfully means "Z_M smooth at M"; `Algebra.IsSmoothAt` is the honest Mathlib abbrev; `[IsAlgClosed k]`
is the honest minimum for the route (no hidden `CharZero`, of any characteristic); the `omit [IsAlgClosed k]`
annotations are correct; the G-action transport, the scheme↔ring bridge, the residue-field equiv, and
non-vacuity (`m_M ≠ ⊤` ⟹ `A` nontrivial ⟹ headline not vacuous) all check out. The orbit-vs-rank-locus
identity is an imported proved equality (L6.4), reconciled in-module — not a silent mismatch.

---

> **Claim (A3 headline, L3).** Over an algebraically closed field, the orbit-closure coordinate ring
> `A = orbitRing M` is formally smooth over `k` at the normal-form point ideal `m_M`.
>
> - **Lean:** `DLNFibre.Core.isSmoothAt_normalFormIdeal`
>   (`lean/DLNFibre/Core/OrbitSmooth.lean` @ `2e931e5`)
> - **Gloss.** `[Field k] [IsAlgClosed k]`; `M : Tuple d`. Then `Algebra.IsSmoothAt k (normalFormIdeal M)`,
>   where `normalFormIdeal M = orbitPointIdeal M 1 = RingHom.ker (orbitEval M 1)` is the point ideal of
>   `canonicalCoord M` in `A = MvPolynomial (RepCoord d) k ⧸ orbitIdeal M`,
>   `orbitIdeal M = vanishingIdeal (orbitSet M)`. `Algebra.IsSmoothAt k p` unfolds (by `rfl`, Mathlib
>   abbrev) to `Algebra.FormallySmooth k (Localization.AtPrime p)`.
> - **Proved.** Smoothness of `Z_M` at `M`, over any algebraically closed field. Route DENSE: the scheme
>   smooth locus of `f = Spec.map (algebraMap k A)` is dense (`dense_smoothLocus_of_perfectField`: perfect
>   `k` + reduced `X = Spec(.of A)`) and open; the orbit closed points are dense (`dense_orbitSpecSet`);
>   `Dense.inter_open_nonempty` gives a smooth orbit `k`-point (`exists_orbitPointIdeal_isSmoothAt`); the
>   scheme↔ring bridge (`orbitScheme_mem_smoothLocus_iff_isSmoothAt`) reads it as
>   `Algebra.IsSmoothAt k (orbitPointIdeal M P)`; the `G_d`-transport (`isSmoothAt_orbitPointIdeal_iff`)
>   carries it to `m_M`.
> - **Assumed.** `[IsAlgClosed k]` (⟹ `PerfectField k` for generic smoothness; ⟹ Jacobson, `k`-points =
>   closed points). The L3 *content* (smoothness of the closure at the normal-form point) is char-free;
>   the `[CharZero k]` of later steps (L2b★) is not used here. `A` is a domain via L1
>   (`isPrime_vanishingIdeal_orbitSet`, needs `[IsAlgClosed k]`).
> - **Cited.** L6.4 (Abeasis–Del Fra orbit-closure = rank locus) and L1 (orbit irreducible) are proved
>   in-repo (`OrbitClosure`, `OrbitVariety`) and consumed as lemmas. Mathlib generic smoothness
>   (`Scheme.Hom.dense_smoothLocus_of_perfectField`), the affine stalk-map ↔ localized-map iso
>   (`Scheme.arrowStalkMapSpecIso`), `Algebra.FormallySmooth.iff_of_equiv`,
>   `IsLocalization.ringEquivOfRingEquiv`/`atUnits` are Mathlib v4.29.
> - **Deferred.** none for L3 itself.
> - **Status.** sorry-free + reviewed

---

> **Claim (A3 deliverable, κ(m_M)=k).** The residue field at `m_M` is `k`: `A ⧸ m_M ≃ₐ[k] k`.
>
> - **Lean:** `DLNFibre.Core.residueFieldNormalFormEquiv`
>   (`lean/DLNFibre/Core/OrbitSmooth.lean` @ `2e931e5`)
> - **Gloss.** `[Field k] [IsAlgClosed k]`; `M : Tuple d`. Then `(orbitRing M ⧸ normalFormIdeal M) ≃ₐ[k] k`.
> - **Proved.** `orbitEval M 1 : A →ₐ[k] k` (the descended evaluation at `canonicalCoord M`) is a
>   surjective `k`-algebra hom (split by `algebraMap k A`) with kernel `m_M`; the first isomorphism theorem
>   (`Ideal.quotientKerAlgEquivOfSurjective`) gives the equiv. `M` is a `k`-rational point.
> - **Assumed.** `[IsAlgClosed k]` (inherited from the section; the equiv itself needs only `[Field k]`).
> - **Cited.** none.
> - **Status.** sorry-free + reviewed

---

> **Claim (A3 bridge).** Scheme↔ring smooth-point dictionary: a point `p` of `Spec A` is in the scheme
> smooth locus of the structure morphism iff `A` is formally smooth at `p` over `k`.
>
> - **Lean:** `DLNFibre.Core.orbitScheme_mem_smoothLocus_iff_isSmoothAt`
>   (`lean/DLNFibre/Core/OrbitSmooth.lean` @ `2e931e5`)
> - **Gloss.** `[Field k]` (`[IsAlgClosed k]` omitted); `p : PrimeSpectrum (orbitRing M)`. Then
>   `(p : orbitScheme M) ∈ (orbitSchemeHom M).smoothLocus ↔ Algebra.IsSmoothAt k p.asIdeal`.
> - **Proved.** Via `Scheme.arrowStalkMapSpecIso` (the stalk map of `Spec.map (algebraMap k A)` at `p` is
>   arrow-iso to `Localization.localRingHom (comap p) p (algebraMap k A)`) + `RingHom.FormallySmooth.respectsIso`;
>   since `k` is a field, `comap p = ⊥` (`comap_algebraMap_eq_bot`) and the source `AtPrime ⊥ ≅ k`
>   (`IsLocalization.atUnits`), so `localRingHom = algebraMap k (AtPrime p)` up to a source iso
>   (`localRingHom_formallySmooth_iff`), whose `FormallySmooth` is `Algebra.IsSmoothAt`
>   (`RingHom.formallySmooth_algebraMap`). No `primeIdealOf`/`isoSpec` hand-rolling.
> - **Status.** sorry-free + reviewed

---

## Module structure (L3.0–L3.4)

- **L3.0** `baseChangeAlgEquiv P : R ≃ₐ[k] R` (pullback composition `baseChangePullback_comp` + inverse
  via `P⁻¹`); descends to `orbitRingAlgEquiv M P : A ≃ₐ[k] A` (`orbitIdeal_map_eq`, the orbit ideal is
  `G_d`-invariant). Point ideals `m_{P•M} = orbitPointIdeal M P` (maximal, prime); transport
  `orbitPointIdeal_eq_comap : m_{P•M} = comap α_P m_M`. Reuses landed `OrbitClosure.baseChangePullback`,
  `eval_baseChangePullback`, `baseChangePullback_mem_vanishingIdeal_orbitSet`.
- **L3.1** `isSmoothAt_orbitPointIdeal_iff : IsSmoothAt k m_{P•M} ↔ IsSmoothAt k m_M` via
  `localizationAtPrimeAlgEquiv` (AtPrime equiv from `α_P`, `IsLocalization.ringEquivOfRingEquiv`) +
  `FormallySmooth.iff_of_equiv`. The smooth locus is `G_d`-stable.
- **L3.2** instances `orbitRing_finitePresentation`, `orbitRing_isJacobsonRing`; Spec model
  `orbitScheme`/`orbitSchemeHom` with `LocallyOfFinitePresentation` + `LocallyOfFiniteType`; sorry-free
  instance `example` (the flagged time sink — resolved cleanly via `HasRingHomProperty.Spec_iff`).
- **L3.3** `dense_orbitSpecSet` — orbit closed points dense in `Spec A`
  (`vanishingIdeal_orbitSpecSet_eq_bot`, a rewrite of L6's ideal equality through the quotient).
- **L3.4** assembly + the bridge (above).

## Non-vacuity

The headline needs `[IsAlgClosed k]`, not satisfiable at `ℚ`. The L3.0/L3.1 transport objects (needing
only `[Infinite k]`) are exercised on the `(2,2,2)/ℚ` tuple `tupleWitnessQ`: two in-file `example`s —
`(orbitEval tupleWitnessQ 1).comp (orbitRingAlgEquiv tupleWitnessQ 1).toAlgHom = orbitEval tupleWitnessQ 1`
and `(normalFormIdeal tupleWitnessQ).IsMaximal`.

## Axiom footprint

`#print axioms` on `isSmoothAt_normalFormIdeal`, `residueFieldNormalFormEquiv`, and
`orbitScheme_mem_smoothLocus_iff_isSmoothAt`: `[propext, Classical.choice, Quot.sound]` only — no
`sorryAx`, no custom axioms. `scripts/sorries` = 0 across the whole library; `lake build` green
(3000 jobs). Zero warnings in `OrbitSmooth.lean`.

## Notes for the route (resolved risks)

- Thread 34 flagged `IsOpen O_M` as the hard sub-lemma and **L3.2 instance plumbing** as the realistic
  time sink. Both dissolved: `IsOpen O_M` is *false as stated* (a set of closed points), replaced by
  `dense_orbitSpecSet` (cheap, from L6); L3.2's instances resolved by `inferInstance`/`Spec_iff` with no
  hand-rolling.
- The genuinely fiddly step was the **affine scheme↔ring bridge**. The clean route (Codex-corroborated,
  artefacts in `expeditions/.../threads/35-A3-orbit-smooth/codex/`) is `Scheme.arrowStalkMapSpecIso`
  (stalk-map of a `Spec.map` ≅ `localRingHom`) — NOT `formallySmooth_stalkMap_iff` + `primeIdealOf`/`isoSpec`
  bookkeeping, which is the noisier path Mathlib's `isOpen_smoothLocus` uses internally.
