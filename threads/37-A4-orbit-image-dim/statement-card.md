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

## A4.3 scaffold — LANDED 0-sorry (`Core/OrbitDifferentialRank.lean`, commit `c6513a8`)

The transpose / trace-pairing factorization of the generic Jacobian, all char-free and axiom-clean
(`[propext, Classical.choice, Quot.sound]`), library green:

- **`deltaT M`** — the entrywise trace transpose `δ⁰ᵀ : cochain1 → cochain0` (a `k`-LinearMap).
- **`pair_deltaT_eq_pair_deformationδ`** — the **adjoint relation** `⟨deltaT ψ, G⟩₀ = ⟨ψ, δ⁰ G⟩₁` for
  any module-valued `G` (both halves; `Finset.sum_dite_eq'` + `Finset.sum_eq_single` collapse the
  dependent `Fin.succ`/`castSucc` casts).
- **`traceFun`/`traceEquiv`** — the entrywise trace **self-duality** of a finite product of matrix
  spaces (nondegenerate via `Pi.single` + `Matrix.single`; `LinearEquiv.ofBijective`).
- **`finrank_range_deltaT`** — the **transpose-rank identity** `finrank(range deltaT) =
  finrank(range δ⁰)`, via the trace self-dualities + `LinearMap.finrank_range_dualMap_eq_finrank_range`.
- **`genUnitK`/`genUnitInvK`/`genFactorK`** (the generic units over `K = FractionRing (groupRing d)`)
  + `genUnitK_mul_inv`, `genFactorK_apply`, `D_genFactorK`, and `D_genericOrbitCoord_eq` (per-coordinate
  connection `D(f_x) = D((V₂ F V₁⁻¹)_{st})`).
- **`mcΘ`** (the Ω-valued Maurer–Cartan `V_v⁻¹ DV_v`) + **`D_orbit_expand`** (the gate expansion of
  `D(f_x)` via `derivMatrix_mul_apply`/`derivMatrix_inv_apply`, `D(genFactorK)=0`) +
  **`genUnitK_smul_mcΘ`** / **`genUnitInvK_smul_genUnitK_smul`** (the left/right Maurer–Cartan collapses).

The base-change rank tool `finrank_range_baseChange` is in `Core/MatrixKaehler.lean` (above).

## Residual — the conjugation identity + final `hA43_le` (kept OUT of the committed file)

To respect the project sorry-gate, two declarations are **NOT** committed (their proofs are written
and validated piece-by-piece but `D_orbit_conj` rests on one inverse-side reindex lemma that did not
elaborate cleanly):

- **`D_orbit_conj`** : `D(f_x) = Σ_a Σ_b (V₂)_{sa} (V₁⁻¹)_{bt} • bracketG (mcΘ M) i a b` — the
  conjugation identity. **Direct-side half `hB` is PROVED** (in the written proof); it rests on:
- **`D_orbit_conj_termA`** (the **inverse / `D(V₁⁻¹)`-side** bracket half) — the sole open lemma.
  Both sides normalise to `− Σ_w Σ_c Σ_e (V₂*genFactorK)_{sw} • (V₁⁻¹_{wc} • (V₁⁻¹_{et} • D(V₁_{ce})))`;
  the RHS flattens `mcΘ`, folds `M_{au}` (k→K via `algebraMap_smul`), and collapses
  `Σ_a V₂_{sa} genFactorK_{au} = (V₂*genFactorK)_{su}` (`Matrix.mul_apply`). The **mirror of the proved
  direct-side `hB`** — mathematically routine.

**Precise obstruction (for the focused follow-up / Codex).** Every PIECE of `termA` was validated in
isolation (`algebraMap_smul` bridge; `Matrix.mul_apply` collapse; `Finset.sum_comm` swaps; per-term
`smul_smul`/`smul_comm`/`module`). The ASSEMBLED proof fails to elaborate three ways: (i) deep
`rw [show … from by …]` nesting hits a parser `expected ']'` ambiguity (the inner `by` block's
extent); (ii) the un-nested `have e1/e2` variant hits per-term `smul`-coefficient `Application type
mismatch` (the bound indices `a : Fin (d i.succ)` vs `b,u,c : Fin (d i.castSucc)` across
`mcΘ`/`V₁ = genUnitK i.castSucc`/`genFactorK`); (iii) a `whnf`/`isDefEq` heartbeat blow-up on the
localized `K = FractionRing (groupRing d)`. **Recommended close:** a single common normal form (a
`Finset.sum` over `Fin (d i.succ) × Fin (d i.castSucc) × Fin (d i.castSucc)` of `coeff • Dk (V₁ c e)`)
on BOTH sides, then ONE `Finset.sum_bij`/`sum_nbij'` reindex — NOT the term-by-term `rw`/`congr`
script attempted (which is what fought the elaborator). Once `termA` closes, `D_orbit_conj` is
immediate (`hsplit` + `hB` + `termA`), and the final `hA43_le` is: `span_K{D(f_x)} = range(Φ.bc)`
for `Φ = (pair-with-mcΘ) ∘ deltaT` (conjugation preserves span; `Φ(e_x) = bracketG(mcΘ)_x` by the
adjoint), then `finrank ≤ finrank(range deltaT.bc) = finrank_k(range deltaT) = finrank_k(range δ⁰)`
(`finrank_range_baseChange` + `finrank_range_deltaT`).

Validated Mathlib bricks (all `#check`ed present): `Module.finrank_baseChange`,
`Submodule.finrank_map_le`, `LinearMap.range_comp`, `LinearMap.finrank_range_dualMap_eq_finrank_range`,
`Finset.sum_dite_eq'`, `Module.Flat.lTensor_preserves_injective_linearMap`, `lTensor_surjective`,
`algebraMap_smul`, `Matrix.single_apply_*`.

The landed dual-number `orbitAction_eps_eq_deformationδ` is a *different* representation (pointwise at
e) and does not shorten this Kähler build; it is the right object for A6.1's R2★.

## Fidelity note (for the reviewer)
The headline `(ringKrullDim …).unbotD 0 ≤ finrank …` is in `ℕ∞` (the `unbotD 0` is `ℕ∞`-valued, RHS
`finrank` coerced). `genericDifferentialRank` is the GENERIC (fraction-field) differential rank — NOT a
pointwise one — so the `t↦t²` / constant-rank soundness trap (thread 33/36) is avoided by construction:
the rank object is over `FractionRing B`, never at a chosen point.
