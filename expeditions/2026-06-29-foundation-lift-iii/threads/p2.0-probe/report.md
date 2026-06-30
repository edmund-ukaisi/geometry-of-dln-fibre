# P2.0 — de-`Tuple` feasibility probe: VERDICT + interface sketch

**Scout, 2026-06-30. Branch `expedition/fl3-p2`. Gates all of Phase 2.**

> **VERDICT: PROCEED** — the orbit-dimension squeeze is abstractable to a reusable DLN-free engine,
> *as a hypothesis-carrying interface*: the two genuinely geometric facts (the Maurer–Cartan
> differential factorisation, and the infinitesimal-action "δ⁰φ kills the orbit ideal") are **inputs**
> the matrix-tuple DLN code **discharges as one instance** — not consequences of a bare orbit map. No step
> is irreducibly `Tuple`-shaped. The core feasibility signal (the A4.3 keystone restated against the
> abstract interface, with **no `cochain`/`Tuple` types**) elaborates cleanly. Decorrelated Codex (xhigh)
> independently returns the same verdict and the same boundary.

The squeeze (recalibrated Phase-2 capstone), with the direction each piece serves:

```
varietyDim 𝒪  =  trdeg  ≤  genericDifferentialRank  ≤  finrank(range δ⁰)  ≤  finrank(cotangent)  =  varietyDim 𝒪
   └────────────── A4 submersion bound (≤) ──────────┘      └────────── A6.1 reverse (≥) ──────────────┘
```

---

## 1. `Tuple`-coupling map

For each load-bearing object, classified **(i)** genuinely abstract / **(ii)** mechanically de-`Tuple`-able
(rename/parameterize) / **(iii)** irreducibly `Tuple`-shaped. Direction-of-squeeze noted. **There are no
(iii) entries** — the candidates resolve to (ii)-with-an-abstract-hypothesis. Object-eq vs `finrank`-eq is
called out where it matters.

### (i) Genuinely abstract — already DLN-free; `Tuple` only instantiates

| object | file | what it is | note |
|---|---|---|---|
| `genericDifferentialRank k B f` | `RingTheory/Kaehler/GenericRank` | `finrank_K (span_K {D_k(f_i)})`, `K=Frac B`; `B` a `k`-domain, `f : ι → B` | the field-theoretic core of A4.3-LHS. **No `Tuple`.** |
| `DiffIndepCriterion` / `diffIndepCriterion_proof` | `…/GenericRank` | char-0 "alg-indep ⟹ differentials lin-indep" | the A4.2 char-0 content, isolated. |
| `trdeg_adjoin_le_genericDifferentialRank` | `Dimension/Trdeg` | `trdeg(adjoin k (range f)).toNat ≤ genericDifferentialRank k B f` | the A4.2 trdeg wrapper; char-free reduction. |
| `derivMatrix_mul_apply` / `derivMatrix_inv_apply` | `RingTheory/Derivation/Matrix` | entrywise Leibniz + `D(U⁻¹)=−U⁻¹(DU)U⁻¹`, general `Derivation R A M` | the matrix-Kähler **gate** used inside A4.3-step-(b). Already abstract. |
| `finrank_range_baseChange` | `LinearAlgebra/BaseChange` | base-change preserves range finrank (V2 variant) | closes A4.3 (`finrank`-eq across `K = Frac R`). |
| `varietyDim Z` | `Dimension/Codimension` | `ringKrullDim(MvPoly σ k ⧸ vanishingIdeal Z).unbotD 0`, any `σ` | both ends of the squeeze. **No `Tuple`.** |
| `ringKrullDim_quotient_unbotD_eq_trdeg_toNat` (+ `…_eq_trdeg_of_fg_domain`) | `Dimension/Localization` | A4.1 in general fg-`k`-domain form | A4.1's general parent; the orbit form is a transport. |
| `finrank_cotangentSpace_eq_of_isSmoothAt` + `Dimension/{Regular,Smooth}` + `CotangentLocalization` | those files | smooth point ⟹ `finrank κ(cotangentSpace) = ringKrullDim(AtPrime m)`; localization collapse | the M3/L2a smooth-side bricks, general `k`-algebra `A`, maximal `m`. **No `Tuple`.** |
| `traceFun`/`traceEquiv`/`finrank_range_deltaT` | `OrbitDifferentialRank` | trace self-duality + transpose-rank, stated for **arbitrary** `{ι}[Fintype ι]{a b : ι → ℕ}` | already not `Tuple`/`cochain`-typed; only need a finite index + shape fns. (`finrank`-eq.) |
| `finrank_range_dualMap_eq_finrank_range` | **Mathlib** | `finrank range f.dualMap = finrank range f`, any `f : V₁ →ₗ[K] V₂` | the deep transpose-rank fact step-(c) rests on. |

### (ii) Mechanically de-`Tuple`-able — incidental encoding; a rename/parameterization frees it

| object(s) | file | what frees it |
|---|---|---|
| `groupRing d`, `genericUnit/Inv`, `genericFactor`, `genericOrbitCoord`, `orbitPullback` | `OrbitVariety` | parameterize on **(coordinate domain `R`, orbit family `fρ : ρ → R`)**. The *constructions* (`Localization.Away` of a det-product; `aeval` of a coordinate family) are generic; the matrix-tuple is the chosen presentation. (serves both ends.) |
| `orbitMap`/`orbitSet`/`range_orbitMap`/`vanishingIdeal_range_orbitMap_eq_ker`/`isPrime_vanishingIdeal_orbitSet` (orbit-as-image irreducibility) | `OrbitVariety` | only uses: an irreducible-domain coordinate ring `R` + an `aeval` pullback; the `⊆` is `MvPolynomial.funext` over an infinite domain (generic). De-`Tuple` = restate on `(R, fρ)`. |
| A0 / A4.1 / A4.4 assembly | `OrbitPullbackDim` / `AffineNoetherRank` / `OrbitImageDim` | orbit specialisations transported through the first-iso `quotientKerEquivRangeOrbitPullback`. The general facts live one layer down. De-`Tuple` = restate on `(R, fρ)` **+ supply the L6.4 ideal-equality `orbitRankLocus = orbitSet` as a hypothesis** (that box-move equality stays DLN-local — see "stays DLN-local"). |
| `OrbitSmooth` L3.0–L3.4 (G-automorphisms, dense orbit, smooth-point transport) | `OrbitSmooth` | the *structure* (a group of `k`-algebra automorphisms of `R⧸I` with a dense orbit of `k`-rational points + perfect-field generic-smoothness density) is generic; the matrix-tuple supplies the concrete `G`-action `baseChangePullback P` and the density `vanishingIdeal_orbitSpecSet_eq_bot`. |
| `OrbitTangentCotangent` R3–R6 (descend `dirDeriv` to `A`, cotangent functional, `finrank cotangent = varietyDim`) | `OrbitTangentCotangent` | generic once you have: `I` prime, a smooth `k`-rational point, a directional-derivative derivation killing `I`. `residueFieldNormalFormEquiv` (`k`-rational point) is a generic surjective-eval iso. |

### (iii) Irreducibly `Tuple`-shaped — **none.** The two candidate spots resolve to (ii)+hypothesis:

| candidate | file | why it is NOT a HALT |
|---|---|---|
| `D_orbit_conj` (A4.3 step b): `D(f_x) = Σ (V₂)_{sa}(V₁⁻¹)_{bt} • bracketG(mcΘ)` | `OrbitDifferentialRank` | This *uses* the orbit coordinate being the **conjugation** `V₂ · F · V₁⁻¹` and the Maurer–Cartan `D(f_x) = bracket of V⁻¹DV`. But that is the geometric identity `dμ_g = d(g·−)_M ∘ dμ_e ∘ dL_g⁻¹` (dually: **`D(orbit coords)` factors through `(dμ_e)* = δ⁰`**) — *general for a smooth algebraic group action*. The squeeze only consumes its **consequence** `span_K{D(f_x)} ≤ range_K(adjoint ∘ δ⁰.baseChange K)`. Package that consequence as a hypothesis; the matrix-tuple instance **discharges** it via `D_genericOrbitCoord_eq` + `D_orbit_conj` + `mcΘ` + the (abstract) matrix-Kähler gate. |
| `pair_deltaT_eq_pair_deformationδ` / `deltaT` (A4.3 step c) | `OrbitDifferentialRank` | `deltaT` is just the transport of `δ⁰.dualMap` across the chosen self-dualities `traceEquiv`. **Confined to one file, consumed nowhere else.** The honest content is `finrank range(δ⁰.dualMap) = finrank range δ⁰` — **Mathlib's**, any finite-dim map. Drop `deltaT`, keep `δ⁰.dualMap` (or carry an abstract `δAdj` with `rank δAdj = rank δ⁰`); step (c) is then generic. |
| `orbitAction_eps_eq_deformationδ` (R2★ certificate) | `OrbitDifferential` | the dual-number `1+εφ` curve whose ε-part is `δ⁰φ`. Abstractly: "for every `φ`, the directional derivative along `δ⁰φ` kills the orbit ideal." Package as the `InfinitesimalAction` hypothesis; the matrix-tuple discharges it (`R2★ = dirDeriv_orbitIdeal_eq_zero`). |

**Stays DLN-local (correctly, by mandate + content):** `OrbitClosure`/`OrbitKostant`/`Orbit` (type-A
Abeasis–Del Fra box-moves), incl. the L6.4 ideal-equality `orbitRankLocus = orbitSet`. The abstract A0 takes
this equality as a hypothesis; only the DLN instance proves it.

---

## 2. Abstract affine-`G`-variety interface — signature sketch

The recommended boundary is a **small** engine (4 hypothesis-carrying bricks + the headline), not a full
algebraic-group framework. (Scratch-elaborated locally, uncommitted; only `sorry` warnings, no type errors.)

```lean
universe u

/-- Abstract affine-`G`-variety interface (the de-`Tuple` carrier). The DLN matrix-tuple is ONE instance. -/
structure AffineGVariety (k : Type u) [Field k] where
  /-- ambient affine-space coordinate index (the `RepCoord` analogue). -/
  ρ : Type
  [ρfin : Fintype ρ]
  /-- group coordinate ring `𝒪(G)`: a finite-type `k`-domain (`groupRing d` is the instance). -/
  R : Type u
  [Rcr : CommRing R] [Rdom : IsDomain R] [Ralg : Algebra k R]
  /-- the orbit-map pullback family `μ* : X⟨coord⟩ ↦ fρ x ∈ 𝒪(G)` (`genericOrbitCoord M` is the instance). -/
  fρ : ρ → R
  /-- deformation carriers `C⁰, C¹` (the `cochain0/cochain1` analogues) + the action map `δ⁰`. -/
  C0 : Type u
  [C0ab : AddCommGroup C0] [C0mod : Module k C0] [C0fin : FiniteDimensional k C0]
  C1 : Type u
  [C1ab : AddCommGroup C1] [C1mod : Module k C1] [C1fin : FiniteDimensional k C1]
  δ : C0 →ₗ[k] C1                                  -- `deformationδ M M` is the instance
```

The two **geometric hypotheses** the engine consumes (the content the instance discharges):

```lean
variable {k : Type u} [Field k] (G : AffineGVariety k)

open scoped TensorProduct

/-- (H1) Maurer–Cartan factorisation: over `K = Frac R`, the span of the orbit-coordinate differentials
    sits in the base-change image of an adjoint carrier `L` composed with `δ.baseChange`.
    DLN discharge: `D_genericOrbitCoord_eq` + `D_orbit_conj` + `mcΘ` + the matrix-Kähler gate. -/
def DifferentialFactors
    (L : (FractionRing G.R ⊗[k] G.C1) →ₗ[FractionRing G.R] KaehlerDifferential k (FractionRing G.R)) :
    Prop :=
  Submodule.span (FractionRing G.R)
      (Set.range fun x : G.ρ =>
        KaehlerDifferential.D k (FractionRing G.R) (algebraMap G.R (FractionRing G.R) (G.fρ x)))
    ≤ LinearMap.range (L.comp (G.δ.baseChange (FractionRing G.R)))

/-- (H2) Infinitesimal-action: every `δ⁰ φ` gives a derivation at the base point killing the orbit ideal.
    Stated abstractly via the directional-derivative functional on `MvPolynomial ρ k`.
    DLN discharge: R2★ `dirDeriv_orbitIdeal_eq_zero` (dual-number `1+εφ`). -/
-- (carrier: an abstract `dirDeriv : C0 → (MvPolynomial ρ k →ₗ[k] k)` derivation-at-base-point,
--  with `dirDeriv φ f = 0` for `f` in the orbit ideal; left as the `CotangentInjection` brick's input.)
```

The four bricks + the headline (signatures; bodies are the de-`Tuple`'d existing proofs):

```lean
-- B1  GenericRankBound : genericDifferentialRank ≤ finrank(range δ)  from (H1) [+ AdjointRank]
example (G : AffineGVariety k)
    (L : (FractionRing G.R ⊗[k] G.C1) →ₗ[FractionRing G.R] KaehlerDifferential k (FractionRing G.R))
    (hMC : DifferentialFactors G L) :
    genericDifferentialRank k G.R G.fρ ≤ finrank k (LinearMap.range G.δ) := sorry

-- B2  AdjointRank : either use `δ.dualMap` directly (finrank_range_dualMap_eq_finrank_range, Mathlib),
--     or carry `δAdj` + `rank δAdj = rank δ`. (No new statement needed if dualMap is used.)

-- B3  CotangentInjection : finrank(range δ) ≤ finrank(cotangent at the base point)  from (H2)
--     (abstract R2★-derivation-kills-ideal ⟹ ker(cotPairing) ≤ ker δ ⟹ the finrank bound).

-- B4  SmoothCotangentDim : finrank(cotangent at base point) = varietyDim Z  from a smooth k-rational point
--     + the (abstract) dimension bridge (M3/L2a/GAP3, already general).

-- HEADLINE  squeeze: varietyDim Z = finrank(range δ), then L7 ⟹ codim = expected codim.
example (G : AffineGVariety k) (Z : Set (G.ρ → k))
    (hle : varietyDim Z ≤ (finrank k (LinearMap.range G.δ) : ℕ∞))
    (hge : (finrank k (LinearMap.range G.δ) : ℕ∞) ≤ varietyDim Z) :
    varietyDim Z = (finrank k (LinearMap.range G.δ) : ℕ∞) :=
  le_antisymm hle hge
```

**Hypotheses the squeeze needs (named):** `[Field k]`; finite-type domain `R` (`EssFiniteType k (Frac R)`,
the A4.2 side-condition); `[CharZero k]` for the A4.2 criterion (the `[PerfectField]` swap is FALSE — banked
Phase-1 finding); `[PerfectField k] [Infinite k]` for the smooth side (no algebraic closedness; `ℝ` qualifies);
the **L6.4 ideal-equality** `vanishingIdeal Z = ker μ*` (for A0) and the two geometric hypotheses (H1), (H2).

---

## 3. The keystone, restated against the interface (the core feasibility signal)

`genericDifferentialRank_genericOrbitCoord_le_finrank_range_deformationδ` (`OrbitDifferentialRank.lean:572`),
the A4.3 bound, restated abstractly. **Scratch-verified to elaborate locally** (uncommitted), body `sorry`
(scratch only — no `sorry` committed); only the expected `sorry` warning, **no type errors, no `cochain`/`Tuple`
type in the statement**:

```lean
example
    (R : Type u) [CommRing R] [IsDomain R] [Algebra k R]
    {ρ : Type} [Fintype ρ] (f : ρ → R)
    {C0 C1 : Type u} [AddCommGroup C0] [Module k C0] [FiniteDimensional k C0]
    [AddCommGroup C1] [Module k C1] [FiniteDimensional k C1]
    (δ : C0 →ₗ[k] C1)
    (L : (FractionRing R ⊗[k] C1) →ₗ[FractionRing R] KaehlerDifferential k (FractionRing R))
    (hspan :                                   -- (H1): the Maurer–Cartan factorisation
      Submodule.span (FractionRing R)
        (Set.range fun x : ρ =>
          KaehlerDifferential.D k (FractionRing R) (algebraMap R (FractionRing R) (f x)))
      ≤ LinearMap.range (L.comp (δ.baseChange (FractionRing R)))) :
    genericDifferentialRank k R f ≤ finrank k (LinearMap.range δ) := by
  sorry
```

It states **cleanly without `cochain`/`Tuple` types**. That is the core feasibility signal:

- LHS `genericDifferentialRank k R f` — already abstract (Phase-1, no `Tuple`).
- RHS `finrank k (range δ)` — abstract `δ : C0 →ₗ[k] C1`, finite-dim spaces.
- The proof body is exactly the existing chain `(1) hgen` → `(2) hSW` → `(3) finrank_mono + finrank_range_baseChange + finrank_range_deltaT`, with `hspan` replacing what the matrix instance proves via `D_orbit_conj`/`mcΘ`/`deltaT`, and `finrank_range_deltaT` replaced by the Mathlib dual-map fact (or kept as the instance's discharge of `AdjointRank`).

(Also scratch-checked: `traceEquiv` elaborates at a bare `{ι}[Fintype ι][DecidableEq ι]{a b : ι → ℕ}` — i.e.
the trace self-duality is **already** non-`Tuple`; and the abstract squeeze headline `le_antisymm` carries no
`Tuple`.)

---

## 4. VERDICT — claim card

**Claim (PROCEED).** The orbit-dimension squeeze
`varietyDim 𝒪 = trdeg ≤ genericDifferentialRank ≤ finrank(range δ⁰) ≤ finrank(cotangent) = varietyDim 𝒪`,
plus orbit-as-image irreducibility, is liftable to a clean, reusable, DLN-free engine stated against an
abstract affine-`G`-variety interface `(R, fρ : ρ → R, δ⁰ : C0 →ₗ[k] C1)`, **provided the engine carries the
two geometric facts as hypotheses** — (H1) the Maurer–Cartan differential factorisation and (H2) the
infinitesimal-action ideal-killing — which the existing matrix-tuple code discharges as the first instance.
**No step is irreducibly `Tuple`-shaped.**

- **Tier/Status:** new · `survived` (stress-tested against the kill-condition below; decorrelated Codex
  concurs; the keystone restatement scratch-elaborates).
- **Evidence:** §1 coupling map; §3 keystone scratch-elaboration; Codex artefact
  `codex/de-tuple-verdict-answer.md`.
- **Kill-condition (stated before confirming):** *some step's STATEMENT cannot be phrased without a
  `cochain`/`Tuple`/`RepCoord` type — i.e. the abstraction would force the matrix-tuple type back into a
  theorem signature (not merely into the discharge of a hypothesis).* Specifically: if `D_orbit_conj`'s
  consequence could NOT be packaged as a hypothesis on `(R, fρ, δ)` but only as a statement quantifying over
  matrix entries, OR if `deltaT`'s rank identity were consumed by something other than the one-file `finrank`
  bound, that would be a HALT.
- **Stress-test (against the kill-condition):**
  1. The keystone signature elaborates with `R, fρ, δ, L, hspan` — no matrix type. Survives.
  2. `traceEquiv`/`deltaT`/`bracketG`/`mcΘ` are confined to `OrbitDifferentialRank.lean` (grep: consumed
     nowhere else), and the rank fact is Mathlib's `finrank_range_dualMap_eq_finrank_range`. Survives —
     the matrix self-duality never escapes into a downstream signature.
  3. The smooth side's abstract bricks (`finrank_cotangentSpace_eq_of_isSmoothAt`, `Dimension/{Regular,Smooth}`,
     `CotangentLocalization`) already take a general `k`-algebra `A`/maximal `m` — no `Tuple`. Survives.
  - Residual risk (NOT a kill, flagged for the type-(iii)-watch review): the abstract (H1)/(H2) carriers
    `L`/`dirDeriv` must be *general enough* to admit the matrix discharge yet *specific enough* to drive the
    bound. The scratch shows the shape works; the de-correlated risk is the **exact** signature of (H2)'s
    derivation-at-base-point carrier — flag for P2.4/P2.5 decorrelated review.

### Rung plan P2.1–P2.6 (dependency order; type-(iii)-watch spots flagged)

| rung | extracts / abstracts | from | risk / review |
|---|---|---|---|
| **P2.1** | trace self-duality + transpose-rank brick (`traceFun`/`traceEquiv`/`finrank_range_deltaT`), general `{ι}{a b}` → its own home; **or** prefer Mathlib `finrank_range_dualMap_eq_finrank_range` directly and drop `deltaT` | `OrbitDifferentialRank` | low — already shape-general; decide drop-`deltaT`-vs-keep at extraction. |
| **P2.2** | the `AffineGVariety` carrier `structure` + `groupRing`/`orbitPullback`/orbit-as-image irreducibility generalised off `BaseChangeGroup` onto `(R, fρ)` | new, modeled on `OrbitVariety` + `OrbitPullbackDim` | keystone of the refactor; the orbit↔ker `MvPolynomial.funext` `⊆` is generic. |
| **P2.3** | A0 + A4.1 + A4.4 assembly restated on `(R, fρ)` + the L6.4 ideal-equality **as a hypothesis** | `OrbitPullbackDim`/`AffineNoetherRank`/`OrbitImageDim` | low-med — transports through the first-iso; supply L6.4 (stays DLN-local). |
| **P2.4** | **B1 `GenericRankBound` [CRUX]** — A4.3 against the interface, with (H1) `DifferentialFactors` as input; **DLN instance discharges (H1)** via `D_orbit_conj`/`mcΘ`/gate | `OrbitDifferentialRank` (572 ln) | **the big de-`Tuple` refactor.** type-(iii)-watch: the exact (H1) signature `L`/adjoint carrier — **decorrelated review.** |
| **P2.5** | **B3 `CotangentInjection` + B4 `SmoothCotangentDim` [CRUX]** — A6.1 against the interface, with (H2) infinitesimal-action + smooth `k`-rational point + dense `k`-orbit as inputs; **DLN instance discharges** via R2★ dual-number + `OrbitSmooth` density | `OrbitTangentCotangent`+`OrbitSmooth`+`OrbitDifferential` (660+552+99) | **CRUX.** type-(iii)-watch: (H2)'s derivation-carrier signature + the "dense `k`-orbit meets smooth locus" over non-alg-closed `k` — **decorrelated review.** |
| **P2.6** | squeeze headline `varietyDim Z = finrank(range δ)` + L7 ⟹ `hVoigt`, assembled on the interface | `VoigtDischarge` | low — `le_antisymm` + ENat cancellation, already abstract. |

**Recommended scope discipline (from Codex + library-building policy):** keep it a *small hypothesis-carrying
engine*, not a full algebraic-group framework (YAGNI: one consumer today, the DLN instance). Namespace-mirror
the eventual Mathlib target so the lift is a file-move. Do **not** claim the Maurer–Cartan / dual-number steps
are consequences of an arbitrary orbit map — they are **named abstract hypotheses**, with the matrix-tuple
formalisation as the first concrete model (name = content).

---

## 5. Decorrelated Codex consult (artefact)

- Prompt: `codex/de-tuple-verdict-prompt.md` · Answer: `codex/de-tuple-verdict-answer.md` (xhigh, read-only).
- Outcome: **PROCEED**, converging with this report — abstractable as a hypothesis-carrying engine; (b) is the
  group-action identity packaged as a hypothesis, (c) is Mathlib dual-map (not `Tuple`-essential), smooth side
  interface-shaped with explicit dense-`k`-orbit/smooth-`k`-point hypotheses; recommended boundary = the small
  4-brick engine. Sharpening banked: the abstraction is valid **only** as hypothesis-carrying — flagged in the
  rung plan as the P2.4/P2.5 type-(iii)-watch for decorrelated review.

---

## Reflection (scout close)

- **Most likely to advance the expedition:** P2.2 (the `AffineGVariety` carrier + orbit-as-image on `(R, fρ)`)
  — it unblocks every downstream rung and is low-risk (the irreducibility argument is already generic).
- **Most likely to break:** P2.4/P2.5 — not the *statements* (those scratch-elaborate) but the **exact
  signature of the (H1)/(H2) carriers** (the adjoint `L`, the abstract derivation-at-base-point). The honest
  residual risk is over- or under-fitting that hypothesis so it either won't drive the bound or the matrix
  instance can't discharge it. Hence both flagged for decorrelated review.
- **Next computation that would clarify:** before P2.4, write the (H1) carrier `L` *concretely for the DLN
  instance* and check `D_orbit_conj` discharges `DifferentialFactors G L` (a scratch `example`, body the
  existing proof) — that pins the exact abstract signature `L` must have, de-risking the crux before the
  refactor commits to it.
