# Statement card — A4 (route-c submersion bound), module A4.1–A4.4

**Thread:** 37-A4-orbit-image-dim (voigt-discharge, AG half, L2b★ route c).
**Pinned commit:** `fbc743c` (branch `expedition/voigt-discharge`).
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

## `dμ_e = δ⁰` core — LANDED (`Core/OrbitDifferential.lean`)

`orbitAction_eps_eq_deformationδ` (PROVED, char-free): over `DualNumber k = k[ε]/(ε²)`,
`(1 + ε φ_{i+1}) · M_i · (1 − ε φ_i) = M_i + ε · (deformationδ M M φ)_i` — the structural `dμ_e = δ⁰`
certificate (thread 36 §2). Plus `liftMat` algebra (`liftMat_mul`/`_sub`/`_one`, `eps_smul_*`) and
`one_add_eps_mul_one_sub_eps` (`(1+εφ)⁻¹ = 1−εφ`). The geometric heart of A4.3, and the **reusable lemma
for the A6.1 R2★ tide** (`D_{δ⁰φ} f = 0`, the dual-number `1 + εφ` curve). Axiom-clean.

## Matrix-Kähler gate + rank brick — LANDED (`Core/MatrixKaehler.lean`, commit `7f22b0a`)

The irreducible matrix-Kähler nugget of route c, built from scratch (Mathlib v4.29 has no
matrix-`Derivation` API). Char-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`):

- `derivMatrix_mul_apply` (PROVED) — entrywise matrix-product Leibniz over `D : Derivation R A M`:
  `D((P*Q) r c) = Σ_s (P r s • D(Q s c) + Q s c • D(P r s))` (`Matrix.mul_apply` + `map_sum` +
  per-term `Derivation.leibniz`).
- **`derivMatrix_inv_apply`** (PROVED) — the matrix-Kähler inverse identity (entrywise):
  `U*W = 1 ⟹ D(W r c) = − Σ_{s,t} W r s • W t c • D(U s t)` (= `D(U⁻¹) = −U⁻¹(DU)U⁻¹`), via
  `D(U·W) = D 1 = 0` (`derivMatrix_inv_aux`) + left-multiply by `W` + `W*U = 1` collapse.
- **`finrank_range_baseChange`** (PROVED) — base change preserves rank:
  `finrank K (range (f.baseChange K)) = finrank k (range f)` (subtype∘rangeRestrict factorization;
  `lTensor_surjective` for the surjection, `Flat.lTensor_preserves_injective_linearMap` for the
  injection, then `Module.finrank_baseChange`). The rank-side tool for the bound.

Products are kept **entrywise** (`Matrix _ _ M`, M a module, has no `Mul`, so a `Matrix _ _ M` cannot
multiply a `Matrix _ _ K`). Instantiate at `R=k, A=K, M=Ω[K⁄k], D=KaehlerDifferential.D k K`.

## Residual — `hA43_le`, route FULLY VALIDATED, mechanical assembly remaining

**`genericDifferentialRank_genericOrbitCoord_le_finrank_range_deformationδ`** :
`genericDifferentialRank k (groupRing d) (genericOrbitCoord M) ≤ finrank k (range (deformationδ M M))`
— char-free. Headline needs only `≤` (chain `varietyDim = trdeg ≤ genericDifferentialRank ≤
finrank δ⁰`); the A4.4 assembly already takes `hA43_le`. The `_charZero` headline depends on this.

**THE CORRECT ROUTE (established this run; the lossy alternatives ruled out).** The naive "span of
the conjugated entries" bound gives `dim cochain0`, NOT `finrank(range δ⁰)` — entry-extraction
collapses the `K`-structure, so the rank reduction is lost. The correct device is the **transpose
(trace-pairing) factorization**, all pieces individually validated in probes this run:

1. **Per-coordinate connection** (probe-validated): `D(algebraMap B K (f ⟨i,s,t⟩)) = D((V₂ F V₁⁻¹) s t)`
   over `K`, with `V₂ = (genericUnit i.succ).map(alg)`, `V₁⁻¹ = (genericUnitInv i.castSucc).map(alg)`,
   `F = (genericFactor M i).map(alg)` (= `M_i` constant, `D F = 0` via `Derivation.map_algebraMap` +
   `IsScalarTower.algebraMap_apply`). `V₂ * V₁⁻¹`-style `= 1` over `K` via `genericUnit_mul_genericUnitInv`
   + `Matrix.map_mul`/`map_one`.
2. **Gate expansion → conjugated bracket** (paper-derived, NOT yet in Lean): applying the gate twice,
   `D(V₂ F V₁⁻¹)_{st} = (V₂ · (Θ₂ F − F Θ₁) · V₁⁻¹)_{st}` with `Θ_v := V_v⁻¹ · D(V_v)` the Ω-valued
   Maurer-Cartan (entrywise, ~60-100 lines of `Finset.sum`/`•` juggling — the next concrete piece).
3. **Conjugation preserves K-span** (NOT yet in Lean): `span_K{D(f_x)} = span_K{(Θ₂F − FΘ₁)_{st}}`
   (V₂, V₁⁻¹ invertible over K ⟹ each entry is a K-combo of the bracket's entries, and vice versa).
4. **Adjoint pairing** (PROVED in probe, the riskiest sub-step — dependent `Fin.succ/castSucc` casts
   collapse via `Finset.sum_dite_eq'` + `Finset.sum_eq_single`): with the explicit transpose
   `deltaT M ψ : cochain0` and `evΘ(φ) = Σ_v Σ_{pq}(φ_v)_{pq} • (Θ_v)_{pq}`,
   `Σ_v Σ_{pq}(deltaT M ψ)_{vpq} • Θ_{vpq} = Σ_i Σ_{st}(ψ_i)_{st} • (Θ₂F − FΘ₁)_{i,st}` (the T1 half
   fully closed; T2 half symmetric). So `span_K{bracket entries} = evΘ_K(range(deltaT.baseChange K))`.
5. **Final chain**: `finrank_K S ≤ finrank_K(range(deltaT.baseChange K))` (`Submodule.finrank_map_le`
   via `LinearMap.range_comp`) `= finrank_k(range deltaT)` (`finrank_range_baseChange`, LANDED)
   `= finrank_k(range δ⁰)` (transpose-rank: `deltaT = (trace-iso)⁻¹ ∘ δ⁰.dualMap ∘ (trace-iso)`, so
   `finrank_range_dualMap_eq_finrank_range`, VERIFIED present; or by hand from the adjoint relation).

Validated Mathlib bricks (all `#check`ed present): `Module.finrank_baseChange`,
`Submodule.finrank_map_le`, `LinearMap.range_comp`, `LinearMap.finrank_range_dualMap_eq_finrank_range`,
`Finset.sum_dite_eq'`, `Module.Flat.lTensor_preserves_injective_linearMap`, `lTensor_surjective`.

**Remaining Lean work: steps 2, 3, the final wiring of 4-5 (~150-200 lines, no conceptual gap).** The
two hardest sub-pieces (the gate, step 1; the adjoint-with-casts, step 4-T1) are DONE. The landed dual-
number `orbitAction_eps_eq_deformationδ` is a *different* representation (pointwise at e) and does not
shorten this Kähler build; it is the right object for A6.1's R2★.

## Fidelity note (for the reviewer)
The headline `(ringKrullDim …).unbotD 0 ≤ finrank …` is in `ℕ∞` (the `unbotD 0` is `ℕ∞`-valued, RHS
`finrank` coerced). `genericDifferentialRank` is the GENERIC (fraction-field) differential rank — NOT a
pointwise one — so the `t↦t²` / constant-rank soundness trap (thread 33/36) is avoided by construction:
the rank object is over `FractionRing B`, never at a chosen point.
