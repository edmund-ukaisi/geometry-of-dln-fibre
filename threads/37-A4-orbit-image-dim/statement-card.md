# Statement card — A4 (route-c submersion bound), module A4.1–A4.4

**Thread:** 37-A4-orbit-image-dim (voigt-discharge, AG half, L2b★ route c).
**Pinned commit:** `43730b7` (branch `expedition/voigt-discharge`).
**Build:** whole `DLNFibre` library green; `scripts/sorries` = 0; all landed theorems
`#print axioms` = `[propext, Classical.choice, Quot.sound]`.

Goal of the module: the route-c submersion bound
`(ringKrullDim (orbitPullback M).range).unbotD 0 ≤ finrank k (LinearMap.range (deformationδ M M))`,
which chains with the landed A0 (`varietyDim_eq_ringKrullDim_range_orbitPullback`) to give
`varietyDim Z_M ≤ finrank(range δ⁰)` (the AG-half submersion inequality of `hVoigt`).

## Landed (PROVED, sorry-free, axiom-clean)

### A4.1 — `Core/AffineNoetherRank.lean` (char-free)
- `trdeg_eq_of_integral_injective` — integral injective `k[Fin s] →ₐ B` (B a k-domain) ⟹
  `trdeg k B = s` (tower additivity `trdeg_add_eq` + `MvPolynomial.trdeg_of_isDomain` + `trdeg_eq_zero`).
- `ringKrullDim_quotient_unbotD_eq_trdeg_toNat` — for a prime `p` of `k[Fin n]`,
  `(ringKrullDim (R/p)).unbotD 0 = (trdeg k (R/p)).toNat` (both = the Noether rank `s`).
- **`ringKrullDim_range_orbitPullback_unbotD_eq_trdeg_toNat`** (headline) — for the f.g. k-domain
  `(orbitPullback M).range`, `(ringKrullDim).unbotD 0 = (Algebra.trdeg k _).toNat`. Transported via
  the landed first-iso + `renameEquiv` reindex `RepCoord d ≃ Fin n`.

### A4.2 infrastructure + reduction — `Core/JacobianTrdeg.lean`
- `genericDifferentialRank k B f` (def) — the shared route-c rank object: `finrank (FractionRing B)`
  of the span of `{D_k(f_i)}` in `Ω[FractionRing B⁄k]`.
- **`mapBaseChange_injective_of_formallySmooth`** (PROVED) — `mapBaseChange k E K` injective for a
  tower `k→E→K` with `[FormallySmooth E K]` (Jacobi–Zariski `exact_δ_mapBaseChange` + the
  `Subsingleton (H1Cotangent E K)` instance). The base-change-injectivity brick.
- **`D_adjoin_mem_span`** (PROVED) — `D_k(x) ∈ span {D_k(g_i)}` for `x ∈ adjoin k (range g)`.
- **`trdeg_adjoin_le_genericDifferentialRank`** (PROVED, conditional on `DiffIndepCriterion`) — the
  trdeg wrapper: `(trdeg k (adjoin k (range f))).toNat ≤ genericDifferentialRank k B f`.
- `DiffIndepCriterion k B` (def, the **scoped obligation**) — `∀ (n) (x : Fin n → FractionRing B),
  AlgebraicIndependent k x → LinearIndependent (FractionRing B) (fun i ↦ D k (FractionRing B) (x i))`.

### A4.4 assembly — `Core/OrbitImageDim.lean`
- `range_orbitPullback_eq_adjoin` — `(orbitPullback M).range = adjoin k (range (genericOrbitCoord M))`.
- `trdeg_range_orbitPullback_le_genericDifferentialRank` — A4.2 in image form, from `DiffIndepCriterion`.
- **`ringKrullDim_range_orbitPullback_le_finrank_range_deformationδ`** — the headline bound from
  `hA42` + `hA43`.
- **`ringKrullDim_range_orbitPullback_le_finrank_range_deformationδ_of_criterion`** — the headline
  with `hA42` discharged to `DiffIndepCriterion`; remaining obligation `hA43` (= A4.3).
- **`varietyDim_orbitRankLocus_le_finrank_range_deformationδ`** — chained with A0:
  `varietyDim Z_M ≤ finrank(range δ⁰)`, conditional on `hA42` + `hA43`.

## Residual open obligations (precise)

1. **`DiffIndepCriterion k (groupRing d)`** (the char-0 differential criterion — A4.2 core). Provable
   per the decorrelated Codex consult (`codex/a42-core-answer.md`), VERDICT "PROVABLE via formal-smooth
   mapBaseChange injectivity": for `x : Fin n → K` alg-indep over char-0 `k`, the differentials
   `{D_k x_i}` are K-independent. Route: `E = IntermediateField.adjoin k (range x)` (or the
   `P = MvPolynomial`-route with `mvPolynomialBasis`), `FormallySmooth E K` from
   `Algebra.FormallySmooth.of_perfectField` (`[PerfectField k]` via `PerfectField.ofCharZero`,
   `[EssFiniteType E K]` via `EssFiniteType.of_comp` from `EssFiniteType k K`), then
   `mapBaseChange_injective_of_formallySmooth` (LANDED here) carries the purely-transcendental basis
   `{D_E x_i}` to `{D_K x_i}`. The single not-packaged-in-Mathlib brick: the `E`-freeness of `Ω[E⁄k]`
   on `{D_E x_i}` for `E` purely transcendental (a localized `mvPolynomialBasis`; or use the P-route
   where `Ω[P⁄k]` IS free via `mvPolynomialBasis` and base-change it). `[CharZero k]` enters ONLY here.
   **CAVEAT (verified, affects the statement):** `Algebra.FormallySmooth.of_perfectField` requires
   `[EssFiniteType E K]`, so the criterion proof needs `[EssFiniteType k (FractionRing B)]` (then
   `EssFiniteType E K` follows by `EssFiniteType.of_comp`). For our application `B = groupRing d`
   (a localization of `MvPolynomial (GroupCoord d) k`, finite type) `EssFiniteType k (FractionRing B)`
   holds (FiniteType → isLocalization → isLocalization, by `EssFiniteType.comp`); but the clean
   `DiffIndepCriterion` as stated does not carry it. The follow-up should either (a) add
   `[EssFiniteType k (FractionRing B)]` to `DiffIndepCriterion` and discharge it for `groupRing d`,
   or (b) prove `FormallySmooth k (FractionRing B)` directly for our localized B without `of_perfectField`.

   **VERIFIED-BUILDABLE (this thread, scratch):** with `[CharZero k]` + `[EssFiniteType k K]`
   (K = FractionRing B; the latter LANDED for `B = groupRing d` as the instance
   `essFiniteType_fractionRing_groupRing`), the FULL injectivity chain compiles:
   `E := IntermediateField.adjoin k (Set.range x)`; `CharZero E` (from `charZero_of_injective_algebraMap`);
   `PerfectField E` (`PerfectField.ofCharZero`); `EssFiniteType E K` (`EssFiniteType.of_comp`);
   `FormallySmooth E K` (`FormallySmooth.of_perfectField`); hence `mapBaseChange k E K` INJECTIVE
   (`mapBaseChange_injective_of_formallySmooth`, LANDED). So the criterion reduces to the SINGLE
   remaining sub-lemma: **`{D_E x_i}` are `E`-linearly independent in `Ω[E⁄k]`** for the
   purely-transcendental `x` (then base-change to `{1 ⊗ D_E x_i}` K-independent, and `mapBaseChange`
   carries them to `{D_K x_i}` via `mapBaseChange_tmul` + `map_D`). That sub-lemma is the localized
   `mvPolynomialBasis`: `E ≅ FractionRing (MvPolynomial (Fin n) k)` (`aevalEquivField`), `Ω[E⁄k]`
   localizes `Ω[MvPolynomial⁄k]` (`KaehlerDifferential.isLocalizedModule_of_isLocalizedModule`), and
   `mvPolynomialBasis` localizes to a basis via `Basis.ofIsLocalizedModule` /
   `LinearIndependent.of_isLocalizedModule`. This is the one self-contained piece left for A4.2.

2. **`hA43`** : `genericDifferentialRank k (groupRing d) (genericOrbitCoord M)
   = finrank k (LinearMap.range (deformationδ M M))` (the A4.3 differential-rank identity, char-free).
   The orbit-map-differential = δ⁰ bridge (`dμ_e = δ⁰`, verified symbolically in thread 36). Codex Q3
   route: a rank-preserving base-change factorization of the cotangent family map through `deformationδ`,
   replacing the pointwise constant-rank argument with one generic K-linear-equivalence calculation
   (`KaehlerDifferential.linearMapEquivDerivation`, `Derivation.liftKaehlerDifferential_comp_D`,
   `map_D`). Not started — the genuine concrete-calculus piece, soundness-load-bearing.

## Fidelity note (for the reviewer)
The headline `(ringKrullDim …).unbotD 0 ≤ finrank …` is in `ℕ∞` (the `unbotD 0` is `ℕ∞`-valued, RHS
`finrank` coerced). `genericDifferentialRank` is the GENERIC (fraction-field) differential rank — NOT a
pointwise one — so the `t↦t²` / constant-rank soundness trap (thread 33/36) is avoided by construction:
the rank object is over `FractionRing B`, never at a chosen point.
