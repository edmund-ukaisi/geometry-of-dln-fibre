# Statement card — thread 17 (fact C, unconditional-modulo-C2(a))

Discharging the commutative-algebra sub-walls of thread-16's conditional generic-smoothness headline,
reducing the open input to a **single named geometric fact** (C2(a)).

## C1 — localizing a reduced ring recovers a component (the reusable CA core)

> **Claim.** For a reduced ring `R` and a prime `q` containing the minimal prime `I` but no other
> minimal prime, the quotient `R → R⧸I` induces a `k`-algebra iso on localizations
> `Loc.AtPrime R q ≃ₐ[k] Loc.AtPrime (R⧸I) (q.map mk)`; consequently `R` is smooth at such a `q` iff
> the component ring `R⧸I` is smooth at the corresponding prime. For a **minimal** prime `I` (its own
> generic point), the "no other minimal prime" hypothesis is free (incomparability).

- **Lean:** `DLNFibre.Core.localizationAtPrimeQuotientAlgEquiv`,
  `isSmoothAt_of_isSmoothAt_quotient_unique_minimalPrime`,
  `isSmoothAt_minimalPrime_of_isSmoothAt_quotient`,
  `isSmoothAt_minimalPrime_of_componentEquiv_domain`
  (`lean/DLNFibre/Core/LocalizationAtComponent.lean` @ `<commit-sha>`)
- **Gloss.** The kernel `I` dies in `Loc.AtPrime R q` (reduced ring: `⋂ⱼ Iⱼ = ⊥`; for `x ∈ I` pick
  `s` in the intersection of the *other* minimal primes but `∉ q`, then `x·s ∈ ⋂ⱼ Iⱼ = ⊥`), so
  `Localization.localAlgHom` is bijective; `FormallySmooth.iff_of_equiv` transfers `IsSmoothAt`.
- **Proved.** All of C1 unconditionally over a reduced Noetherian `R` (`[IsReduced R]`,
  `[IsNoetherianRing R]`, `[Algebra k R]`). Axiom-clean.
- **Assumed.** `R` reduced + Noetherian; `I ∈ minimalPrimes R`. Both hold for `sweepFibreRing`.
- **Cited.** none (only Mathlib).
- **Deferred.** none for C1.

## C2 — `IsSmoothAt` of `sweepFibreRing` (conditional on C2(a))

> **Claim.** If a top-dim minimal prime `I` of `sweepFibreRing` has a `k`-algebra iso
> `sweepFibreRing⧸I ≃ₐ[k] orbitRing M` (the geometric fact **C2(a)**), then `sweepFibreRing` is
> `IsSmoothAt k I`.

- **Lean:** `DLNFibre.Core.isSmoothAt_sweepFibre_of_component_orbitSmooth`
  (`lean/DLNFibre/Core/FibreGenericSmoothUncond.lean` @ `<commit-sha>`); `[IsAlgClosed k]`.
- **Gloss.** `orbitRing M` is a finitely-presented domain `IsSmoothAt k (normalFormIdeal M)`
  (`OrbitSmooth.isSmoothAt_normalFormIdeal`); a domain smooth somewhere is smooth at its generic
  point `⊥` (`isSmoothAt_bot_of_isSmoothAt`); transport `⊥` across the C2(a) iso and apply the C1
  bridge.
- **Proved.** The whole chain *from* the iso `e`, unconditionally. `sweepFibreRing` reduced
  (`vanishingIdeal_isRadical`, needs `[IsAlgClosed k]`) + Noetherian — both as instances.
- **Assumed.** the C2(a) iso `e : sweepFibreRing⧸I ≃ₐ[k] orbitRing M`.
- **Cited.** none.
- **Deferred (C2(a)).** the iso `e` — identifying a top component of the fibre with an orbit closure.
  NOT in the harness: the θ-count is established via codimension/`ncard` chains, never labelling a
  component by an orbit. Codex-confirmed multi-module wall (~800–2000 lines); needs a
  `fibre-component ↔ orbit-closure` theory (probe lemma `topDim_sweepFibre_component_equiv_orbitRing`).

## C3 — transport to the source pivot chart `Away chartDsig` (LANDED, conditional on the same input)

> **Claim.** Given `IsSmoothAt k q (sweepFibreRing)` at a top-component prime, the source pivot chart
> `Away (chartDsig d r)` is `IsSmoothAt k p` at every chart prime `p` off a smooth witness `h`.

- **Lean:** `DLNFibre.Core.isSmoothAt_chartDsig_of_isSmoothAt_sweepFibre`
  (+ keystones `awayTensorRightAlgEquiv`, `schurTensorAwayAlgEquiv`,
  `exists_smooth_localizationAway_chartDsig_of_isSmoothAt_sweepFibre`,
  and `LocalizationAtComponent.smooth_localizationAway_symm_of_smooth_localizationAway`)
  (`lean/DLNFibre/Core/FibreGenericSmoothUncond.lean` @ `<commit-sha>`); `[IsAlgClosed k] [Infinite k]`.
- **Gloss.** thread-16 gives `g ∉ q` with `Smooth k (SchurLoc ⊗ Away g)`; `schurTensorAwayAlgEquiv`
  identifies this with `Smooth k (Away (1⊗g))` in `SchurLoc ⊗ sweepFibreRing`; the banked chart iso
  + the abstract `Smooth (Away ·)` transport + the basic-open bridge land `IsSmoothAt` of the chart.
- **Proved.** the transport unconditionally, *from* `IsSmoothAt k q (sweepFibreRing)`.
- **Assumed.** `IsSmoothAt k q (sweepFibreRing)` (discharged-modulo-C2(a) by C2).
- **Cited.** none.
- **Deferred.** none for C3 (the only remaining open input across the whole chain is C2(a)).

## Net state

The generic-smoothness chain is now **unconditional except for the single geometric fact C2(a)**
(`sweepFibreRing⧸I ≃ₐ[k] orbitRing M`). All commutative-algebra sub-walls (the reducedness route,
the generic-prime uniqueness, the tensor-localization transport, the chart basic-open) are LANDED,
axiom-clean (`[propext, Classical.choice, Quot.sound]`). C1 is a fully reusable CA brick.

## Status

sorry-free (pending reviewer fidelity check).
