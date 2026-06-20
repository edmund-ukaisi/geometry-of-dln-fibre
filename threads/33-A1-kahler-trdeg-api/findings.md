# Thread 33 (A1) — Mathlib v4.29 API map for the L2b★ route-c build

**Scope.** Pin the exact Mathlib v4.29 + landed-`Core` API that determines the route-c discharge of
`hVoigt` (AG half), and give an honest module count + the hardest must-build lemma. Mathlib pinned at
`v4.29.0` (`lean/.lake/packages/mathlib`, toolchain `leanprover/lean4:v4.29.0` — confirmed).

Route-c chain (from thread 30):

> `varietyDim(Z_M) = ringKrullDim(image μ_M^*) = trdeg(image) ≤ finrank(range δ⁰)`.

Every PRESENT row below compiles in `lean/DLNFibre/Scratch/{KahlerTrdegProbe,RingKrullTrdegProbe}.lean`
(scratch only, not in the library aggregator). Every ABSENT row was checked by exhaustive grep over
`Mathlib/`.

---

## Verdict (headline)

- **Cheapest route: route-c (≈ route B, the Noether-rank + Jacobian-criterion route), 4 modules
  remaining** on top of the already-landed `Core.OrbitPullbackDim` (the A0 link). Route A (the pure
  Kähler `rank Ω = trdeg` route) is strictly more expensive — it needs *two* heavyweight absent
  global bridges instead of one. The thread-30 "route-c = 4 modules" estimate **holds**, and my
  decorrelated Codex consult (`codex/route-c-sizing-answer.md`) independently confirmed **4 remaining
  modules**.
- **The 4-vs-7 swing resolves DOWN to 4** (route-c), *not* the 7 of the "smooth quotient G → O_M"
  route. The lever is real: the explicit linear structure (image = range of an aeval, `δ⁰` an explicit
  matrix-commutator linear map) lets the differential be identified by hand rather than via scheme
  quotients.
- **Single hardest must-build lemma:** the **orbit-map differential-rank bridge** — *not*
  `ringKrullDim = trdeg`. Concretely: `trdeg_k(image μ_M^*) ≤ finrank_k(range δ⁰)`, which forces a
  **char-0 Jacobian criterion** (algebraic independence of image coordinates ⇒ generic differential
  independence) **plus** a constant-rank argument (the rank at the identity = the generic rank, valid
  because the orbit map is homogeneous under the `G`-action). Both pieces are ABSENT in Mathlib.
- **Critical red-team caveat (Codex, confirmed):** the naive "pointwise differential rank ≥ image
  dimension" is **false** in general — `t ↦ t²` has image dimension 1 but differential rank 0 at the
  origin. The orbit map is rescued only by **homogeneity** (constant rank under `G`), so the
  identity-point rank equals the generic rank. Any build plan that bounds `trdeg` by the
  *identity-point* differential rank without the constant-rank step is **unsound**. This is where
  CharZero earns its keep (it rules out the Frobenius `𝔾ₐ ↷ 𝔸¹, t·x = x+tᵖ` inseparable failure).

---

## API table

### 1 · `ringKrullDim = trdeg` for an f.g. domain — **ABSENT as a named lemma, but a cheap corollary here**

| Claim | Mathlib / Core name | Status · signature |
|---|---|---|
| `ringKrullDim A = trdeg k A` (f.g. domain) packaged | — | **ABSENT.** No file in `Mathlib/` mentions both `ringKrullDim`/`krullDim` and `trdeg` (verified: empty grep intersection). |
| `dim(R/p) = noetherRank s` (s = # alg-indep gens) | `Core.PolynomialDimension.ringKrullDim_quotient_eq_noetherRank` | **PRESENT (landed).** `∃ s ≤ n, (∃ g : k[Fin s] →ₐ[k] (R/p), Inj g ∧ g.IsIntegral) ∧ ringKrullDim (R/p) = (s : WithBot ℕ∞)`. |
| `trdeg_k k[Fin s] = s` | `MvPolynomial.trdeg_of_isDomain` | **PRESENT.** `[IsDomain S] : trdeg S (MvPolynomial ι S) = lift #ι`. |
| tower additivity `trdeg_k S + trdeg_S A = trdeg_k A` | `trdeg_add_eq` (root ns) | **PRESENT.** `[Nontrivial R][NoZeroDivisors A][FaithfulSMul R S][FaithfulSMul S A][IsScalarTower R S A]`. |
| algebraic ⇒ `trdeg = 0` | `trdeg_eq_zero` / `trdeg_eq_zero_iff` | **PRESENT.** `[Algebra.IsAlgebraic R A] : trdeg R A = 0`. |

**Reading.** The *named* `ringKrullDim = trdeg` is absent, but we never need it as such: the landed
`ringKrullDim_quotient_eq_noetherRank` gives `dim(image) = s`, and `trdeg_add_eq` + `trdeg_of_isDomain`
+ `trdeg_eq_zero` give `trdeg_k(image) = s` for the **same** `s` (the integral injective
`k[Fin s] →ₐ image` makes `image` algebraic over the polynomial subring, so `trdeg_{subring} image = 0`).
Hence `ringKrullDim(image) = trdeg_k(image)` is a **one-module corollary**, not the bottleneck.

### 2 · Transcendence-degree API — **PRESENT (rich)**

| Claim | Mathlib name (root ns unless noted) | Signature |
|---|---|---|
| trdeg as a `Cardinal` | `Algebra.trdeg` (`@[stacks 030G]`) | `Algebra.trdeg R A : Cardinal` |
| finiteness for f.t. over a domain | `trdeg_lt_aleph0` | `[IsDomain R][FiniteType R S] : trdeg R S < ℵ₀` |
| monotone under inj/surj AlgHom | `trdeg_le_of_injective` / `trdeg_le_of_surjective` | `(f : A →ₐ[R] A') → Inj/Surj ⇑f → trdeg R A ≤/≥ trdeg R A'` |
| equiv invariance | `AlgEquiv.trdeg_eq` | `(e : A ≃ₐ[R] A') : trdeg R A = trdeg R A'` |
| tower additivity (domain) | `trdeg_add_eq` (`@[stacks 030H]`) | see row above |
| transcendence basis | `IsTranscendenceBasis`, `exists_isTranscendenceBasis`, `IsTranscendenceBasis.cardinalMk_eq_trdeg` | `exists_…`: `[FaithfulSMul R A] : ∃ s, IsTranscendenceBasis R (Subtype.val)` |
| `trdeg ≤ #s` when algebraic over `adjoin R s` | `Algebra.IsAlgebraic.trdeg_le_cardinalMk` | `[Algebra.IsAlgebraic (adjoin R s) A] : trdeg R A ≤ #s` |
| integral ⇒ alg-indep transfer | `Algebra.IsIntegral.algebraicIndependent_iff` | `[Algebra.IsIntegral R S]` — relates alg-indep upstairs/downstairs (in `AlgebraicIndependent/AlgebraicClosure.lean`) |

### 3 · Kähler differentials / `rank Ω` — **Ω-of-polynomial PRESENT; field-extension `rank Ω = trdeg` ABSENT**

| Claim | Mathlib name | Status |
|---|---|---|
| `Ω[k[σ]/k]` free with basis `{dx_i}` | `KaehlerDifferential.mvPolynomialBasis` | **PRESENT.** `Module.Basis σ (k[σ]) Ω[k[σ]/k]`. |
| `Ω[S/k]` module-finite for ess-finite-type | `KaehlerDifferential.finite` | **PRESENT.** `[EssFiniteType R S] : Module.Finite S Ω[S/k]`. |
| `Ω[S/k]` free of rank `n` for `IsStandardSmooth` | (used in) `Core.SmoothLocalRelativeDimension.rank_kaehler_eq_finrank` | **PRESENT (landed reuse).** `Module.rank S Ω[S/k] = finrank S Ω[S/k]`. |
| **`rank Ω[L/k] = trdeg k L`** for sep/char-0 field ext | — | **ABSENT.** No `FieldTheory/*` file connects `KaehlerDifferential`/`Ω` rank with `trdeg`. The only field-Kähler facts present are "Ω subsingleton ⇔ separable/unramified" (in `Unramified/*`), not a rank-equals-trdeg theorem. |
| `trdeg ≤ rank Ω` (one direction) | — | **ABSENT.** |

### 4 · Jacobian rank ⇒ trdeg / generic rank — **the bridge is ABSENT**

| Claim | Mathlib name | Status |
|---|---|---|
| `MvPolynomial.pderiv` (partials) | `MvPolynomial.pderiv` | **PRESENT** (and `mvPolynomialBasis_repr_apply` ties `Ω`-coords to `pderiv`). |
| submersive-presentation Jacobian (square det) | `Algebra.PreSubmersivePresentation.jacobiMatrix` / `.jacobian` | **PRESENT** but **square-det** flavour (étale/standard-smooth), *not* a rectangular-rank-of-Jacobian tool. |
| cotangent = ker(Jacobian) at a rational point | `Core.CotangentJacobian` (landed) | **PRESENT (landed).** `finrank k (CotangentSpace (Localization.AtPrime m_A)) = finrank k (ker jacobian)` — but this is for the **variety side** (`Z_M`), via the conormal sequence; it is the smooth-ladder L2a, *not* the image-trdeg route. |
| **Jacobian criterion: alg-indep ⇒ generic differential independence** | — | **ABSENT.** No file connects `AlgebraicIndependent`/`trdeg` with `pderiv`/`Derivation`/`KaehlerDifferential`. This is the load-bearing missing brick for route-c. |
| **generic differential rank = identity differential rank** (constant rank under group action) | — | **ABSENT** (orbit-specific; must build by hand). |

### 5 · First-iso + domain-dim tooling — **PRESENT (and landed)**

| Claim | Mathlib / Core name | Status |
|---|---|---|
| AlgHom first-iso `R/ker ≃ₐ range` | `RingCon.quotientKerEquivRangeₐ` (root via `open RingCon`); `Ideal.quotientKerEquivRange` | **PRESENT.** Already used in `Core.OrbitPullbackDim.quotientKerEquivRangeOrbitPullback`. |
| `ringKrullDim` invariant under integral injective | `Core.IntegralDimension.ringKrullDim_eq_of_integral_injective` | **PRESENT (landed).** |
| `ringKrullDim` invariant under `RingEquiv` | `ringKrullDim_eq_of_ringEquiv` (Mathlib) | **PRESENT.** |
| affine-domain equidimensionality | `Core.AffineDomainDimension.affine_domain_height_add_ringKrullDim_quotient_eq` | **PRESENT (landed).** |
| `dim k[Fin n] = n` | `Core.IntegralDimension.ringKrullDim_mvPolynomial_fin_field` | **PRESENT (landed).** |
| **A0 link: `varietyDim Z_M = ringKrullDim((μ_M^*).range)`** | `Core.OrbitPullbackDim.varietyDim_eq_ringKrullDim_range_orbitPullback` | **PRESENT (landed, this expedition).** `[IsAlgClosed k] : varietyDim (canonicalCoord d '' orbitRankLocus M) = (ringKrullDim (orbitPullback M).range).unbotD 0`. |
| `(orbitPullback M).range` is a domain | `Core.OrbitPullbackDim.isDomain_range_orbitPullback` | **PRESENT (landed).** |

---

## The concrete A4 build plan (4 modules)

The remaining obligation, with A0 landed, is exactly:

    (ringKrullDim (orbitPullback M).range).unbotD 0  ≤  finrank k (LinearMap.range (deformationδ M M))

(LHS = `varietyDim Z_M` by A0; RHS = the linear codimension's complement, `finrank(range δ⁰)`, the
quantity `orbitLinearCodim` subtracts from `finrank C¹`.)

### Module A4.1 — `Core/AffineNoetherRank.lean` — `ringKrullDim(range) = trdeg_k(range)`
- **Reuse:** `ringKrullDim_quotient_eq_noetherRank` (landed) for the `s`; `MvPolynomial.trdeg_of_isDomain`,
  `trdeg_add_eq`, `trdeg_eq_zero`, `AlgEquiv.trdeg_eq` (Mathlib). The integral injective
  `k[Fin s] →ₐ (R/p)` from the Noether engine gives both `dim = s` and (via `IsIntegral ⇒ IsAlgebraic`
  + tower) `trdeg = s`.
- **Build from scratch:** the `Cardinal`/`Nat` ↔ `WithBot ℕ∞` bookkeeping to land
  `ringKrullDim(image) = ((trdeg_k image).toNat : WithBot ℕ∞)` (or, cleaner, prove both equal the
  *same* explicit `s`). ~1 module, low risk.
- **Verdict:** comparatively easy — this is **not** the hard part (despite "ringKrullDim = trdeg"
  sounding scary). The Noether engine already did the dimension work.

### Module A4.2 — `Core/JacobianAlgIndependence.lean` — char-0 Jacobian criterion **(HARDEST)**
- **Statement (target):** for `f : Fin m → k[σ]` (or into a domain), if the differentials
  `{ d f_i }` are `Frac`-linearly independent at the generic point (rank of the Jacobian / of the
  pulled-back `Ω`-images), then `{ f_i }` are algebraically independent — equivalently
  `trdeg_k (adjoin k (range f)) ≤ rank of the differential`.
- **Reuse:** `KaehlerDifferential.mvPolynomialBasis` + `mvPolynomialBasis_repr_apply` (ties `Ω`-coords
  to `pderiv`), `PerfectField.ofCharZero` / `IsAlgClosed → PerfectField` for separability,
  `KaehlerDifferential.finite`, the `trdeg`/`IsTranscendenceBasis` API.
- **Build from scratch:** the criterion itself. This is the genuinely new content and is **char-0
  essential** (Frobenius counterexample in char p). Mathlib has *no* `AlgebraicIndependent ↔ Jacobian
  rank` lemma. Realistic: ~1 module but **high risk / high effort** — it is the standard char-0
  "differentials detect algebraic independence" theorem, and proving it cleanly may itself want the
  `rank Ω[L/k] = trdeg` fact (route A's missing brick) for the function field, so this module may
  *internally* re-derive a slice of route A.
- **Verdict:** **the single hardest must-build lemma.** Flag for the formaliser as the de-risking
  priority; consider a pen-and-paper certificate (witness/obstruction seat) before formalising.

### Module A4.3 — `Core/OrbitDifferentialRank.lean` — `dμ_M at e = δ⁰` + constant rank
- **Statement:** the Jacobian of `orbitPullback M` (the `pderiv` matrix of `genericOrbitCoord`)
  evaluated at the **identity** group point equals `deformationδ M M` (the explicit commutator map
  `φ ↦ (φ_{i+1} M_i − M_i φ_i)`); and the rank is **constant** over `G` (homogeneity), so the
  generic rank used in A4.2 equals `finrank(range δ⁰)`.
- **Reuse:** `deformationδ_apply` (landed `rfl`-simp), the explicit `genericOrbitCoord` definition,
  `eval_genericMat`, `groupPoint` (landed in `OrbitVariety`). The matrix-product-by-`pderiv`
  computation is mechanical but fiddly (the `P⁻¹` factor differentiates to `−φ`).
- **Build from scratch:** the `pderiv`-of-`genericOrbitCoord` = commutator identity, and the
  constant-rank/homogeneity transport. ~1 module, **medium risk** (the matrix calculus is concrete
  but the constant-rank step needs the `G`-translation argument). **This is the second-hardest** and
  is where Codex's red-team caveat bites — without constant rank the whole bound is unsound.

### Module A4.4 — `Core/OrbitImageDimensionBound.lean` — assemble
- **Statement:** `ringKrullDim((orbitPullback M).range) ≤ finrank k (LinearMap.range (deformationδ M M))`,
  then chain with A0 to discharge the `hVoigt` `≥`-half:
  `varietyDim Z_M ≤ finrank(range δ⁰)`.
- **Reuse:** A4.1 (`= trdeg`), A4.2 (`trdeg ≤ generic Jacobian rank`), A4.3 (`generic rank = finrank
  range δ⁰`), plus the landed easy `≤` direction (`range δ⁰ ⊆ ker Jac`) to upgrade to equality if
  desired. ~1 module, low risk (pure glue).

**Total: 4 new modules** (A4.1–A4.4), on top of the landed A0 (`OrbitPullbackDim`). Route-c grand
total = 5 files, 4 remaining. **Confirms the thread-30 estimate.**

### What is reused vs built from scratch (summary)
- **Reused (landed Core):** `ringKrullDim_quotient_eq_noetherRank`, `ringKrullDim_eq_of_integral_injective`,
  `ringKrullDim_eq_of_ringEquiv`, the whole A0 link, `deformationδ`/`deformationδ_apply`,
  `genericOrbitCoord`/`eval_genericMat`, `orbitLinearCodim` framing.
- **Reused (Mathlib):** full `trdeg` API (§2), `KaehlerDifferential.mvPolynomialBasis` + `pderiv`
  link, `PerfectField.ofCharZero`, `Algebra.IsIntegral.algebraicIndependent_iff`,
  `RingCon.quotientKerEquivRangeₐ`.
- **Built from scratch:** A4.2 (Jacobian criterion, char-0) — **hardest**; A4.3 (`dμ_e = δ⁰` +
  constant rank) — second-hardest, holds the soundness; A4.1 + A4.4 — easy corollary + glue.

---

## Honest verdict on the 4-vs-7 swing

The swing resolves to **4**. Route-c is the cheap branch because the explicit linear/aeval structure
of the orbit map lets the differential be computed by hand (A4.3) rather than via a scheme quotient
`G/Stab` (the 7-module branch (b) in the thread-30 codex). The catch the count hides: **one of those 4
modules (A4.2, the char-0 Jacobian criterion) is genuinely hard and may internally re-derive a slice
of the "rank Ω = trdeg" content** that route A would have paid for up front. So "4 modules" is honest
as a *file count* but the **difficulty is concentrated in A4.2**; treat it as the de-risking gate, not
A4.1.

CharZero is a single localized hypothesis on the discharging theorem (the `Core` dimension stack and
A0 are char-free apart from the `IsAlgClosed` the L1/L6.4 bricks force). It enters **only** at A4.2/A4.3
(separability / no-Frobenius), exactly as predicted.

---

## Scratch artefacts (not in the aggregator)
- `lean/DLNFibre/Scratch/KahlerTrdegProbe.lean` — compiles the PRESENT §2/§3/§5 rows (`#check`s).
- `lean/DLNFibre/Scratch/RingKrullTrdegProbe.lean` — compiles the trdeg-bridge pieces for A4.1.
- `threads/33-A1-kahler-trdeg-api/codex/route-c-sizing-{prompt,answer}.md` — decorrelated Codex
  sizing (independently lands "route-c, 4 remaining modules"; supplied the `t↦t²` red-team caveat).
