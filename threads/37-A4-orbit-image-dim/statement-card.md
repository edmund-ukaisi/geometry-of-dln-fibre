# Statement card — A4 (route-c submersion bound), module A4.1–A4.4

**Thread:** 37-A4-orbit-image-dim (voigt-discharge, AG half, L2b★ route c).
**Pinned commit:** `c0e4569` (branch `expedition/voigt-discharge`).
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

## Obligation 1 — DISCHARGED (A4.2 `DiffIndepCriterion`, char 0)

`DiffIndepCriterion k (groupRing d)` is now **PROVED** (`diffIndepCriterion_groupRing`, char 0), so the
A4.2 obligation is gone. The proof (`diffIndepCriterion_proof`, `[CharZero k] [EssFiniteType k
(FractionRing B)]`):
- **base case** `linearIndependent_D_X_fractionRing` (char-free): in `Frac(MvPolynomial (Fin n) k)`,
  `{D(algebraMap X_i)}` independent, via `KaehlerDifferential.isLocalizedModule_map` (`Ω` of a
  localization is the localized `Ω`) + `LinearIndependent.of_isLocalizedModule` on `mvPolynomialBasis`;
- embed `Pf = Frac(MvPoly)` in `K = FractionRing B` by `IsFractionRing.liftAlgHom` of the injective
  `aeval x`; `FormallySmooth Pf K` (`of_perfectField`, `EssFiniteType Pf K` by `of_comp`) ⟹
  `mapBaseChange k Pf K` injective (landed helper);
- flat base change (`Module.Flat.linearIndependent_one_tmul`) of the base case + `mapBaseChange_tmul`
  / `map_D` / `lift_algebraMap` carry `{1 ⊗ D_Pf X_i}` to `{D_K x_i}`.
`EssFiniteType k (FractionRing (groupRing d))` is the landed instance `essFiniteType_fractionRing_groupRing`.
All axiom-clean.

## Residual — ONE obligation (A4.3, the `≤` direction only)

**`genericDifferentialRank k (groupRing d) (genericOrbitCoord M) ≤ finrank k (LinearMap.range
(deformationδ M M))`** — char-free. The headline needs only this `≤` (Codex Q3: the chain is
`varietyDim = trdeg ≤ genericDifferentialRank ≤ finrank δ⁰`, so the equality `hA43` is NOT needed; the
A4.4 assembly now takes `hA43_le`). The char-0 `_charZero` headline depends on this single residual.

Codex route (`codex/a43-answer.md`, VERDICT "PROVABLE, ~6-8 lemmas; scope to the `≤`-bound"): a generic
tangent factorization `orbitJacobianK M = ρ(Pgen) ∘ δK ∘ τ(Pgen)` (`δK` = base change of `deformationδ
M M` to `K`; `ρ`, `τ` the target/domain trivialization isos), then `genericDifferentialRank` = range
rank of `orbitJacobianK` via cotangent duality (`LinearMap.finrank_range_dualMap_eq_finrank_range`,
`Subspace.dual_finrank_eq`), bounded by `finrank K (K ⊗ range δ⁰) = finrank k (range δ⁰)`
(`Module.finrank_baseChange`). Differentiate `genericUnit v * genericUnitInv v = 1` for
`d(P⁻¹) = -P⁻¹ dP P⁻¹` rather than expanding the adjugate. Soundness-load-bearing (the homogeneity /
`dμ_e = δ⁰` content); not started — the genuine concrete matrix-Kähler-calculus piece. Recommended
scoped residual name: `genericDifferentialRank_genericOrbitCoord_le_finrank_range_deformationδ`.

## Fidelity note (for the reviewer)
The headline `(ringKrullDim …).unbotD 0 ≤ finrank …` is in `ℕ∞` (the `unbotD 0` is `ℕ∞`-valued, RHS
`finrank` coerced). `genericDifferentialRank` is the GENERIC (fraction-field) differential rank — NOT a
pointwise one — so the `t↦t²` / constant-rank soundness trap (thread 33/36) is avoided by construction:
the rank object is over `FractionRing B`, never at a chosen point.
