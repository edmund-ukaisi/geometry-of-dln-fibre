# Thread 31 — irreducible-bypass route to `hSweep`: SPECIFY + crux adjudication

*Seat: pen-and-paper, witness direction. FINAL TASK (supersedes orbit-dim, set-level, fibration-dim
briefs — controller voided the latter two). SPECIFY the irreducible-bypass route (one top component
`F_0` → `closure(H·F_0)` irreducible → `trdeg_add_eq` → no-jump `relative_trdeg = dim F_0`). The crux:
is the no-jump residual reachable from the LANDED generic-freeness MODULE case, or does it need the
algebra case (the wall)? Read-only — no Lean writes, no builds. Decorrelated xhigh Codex fired.*

## CRUX VERDICT (one line)

**The no-jump residual `relative_trdeg = dim F_0` WALLS via the trdeg-tower as stated** — the LANDED
generic-freeness MODULE case does NOT fire on the algebra map `O(Mat^{=r}) → O(Z_0)` (relative
dimension positive ⟹ not module-finite), and closed-fibre homogeneity alone does NOT identify the
*generic* fibre (which lives over `Spec K(Mat^{=r})`, not a `k`-point). The no-jump is reachable ONLY
by importing the explicit **gauge-trivialization** `Z_0|_U ≅ U × F_0` — and *that does NOT need
algebra-case generic freeness* — **but once the trivialization is built, `dim Z_0 = δ + dim F_0` reads
directly off the LANDED `MvPolynomial.ringKrullDim_of_isNoetherianRing`, so the trdeg-tower wrapper is
REDUNDANT.** Net: the "irreducible bypass via trdeg-tower" COLLAPSES to the chart-trivialization route
(my prior fibration-dim design) PLUS an extra component-reduction layer (`F_0`, `Z_0`, max-over-union)
— i.e. **MORE modules (~9-11), not fewer**, than the direct chart-trivialization (~7). The trdeg-tower
is not a shortcut; the trivialization is the irreducible content, and it is the same content either way.

**FIRM module estimate, firming up the "~5-8 vs ~12-20" uncertainty:**
- **Direct gauge-trivialization route (no component reduction, no trdeg-tower)** — `Σ^r_Δ ≅ Mat^{=r}_Δ
  × F` per chart, `+δ` via `ringKrullDim_of_isNoetherianRing`, glue: **~7 modules** (my prior design,
  which the trdeg-tower analysis now re-confirms as the floor).
- **Irreducible-bypass-via-trdeg-tower** (this brief's route): the trivialization (same ~4-5 core
  modules) + component reduction to `F_0`/`Z_0` + max-over-union + the custom product/base-change trdeg
  lemma: **~9-11 modules** — strictly heavier, because it does everything the direct route does PLUS
  the component bookkeeping and a redundant trdeg layer.
- **Closed-fibre trdeg-tower WITHOUT the trivialization:** WALLS — needs the algebra-case generic
  freeness / relative Noether normalization over a domain (EGA IV 6.9.1), absent at v4.29, a
  sub-expedition (~12-20).

**So: BUILD the direct ~7-module gauge-trivialization, NOT the trdeg-tower bypass.** The bypass's only
new idea (pass to an irreducible component to get a domain) buys nothing the radical-insensitive
set-level trivialization didn't already give for free.

---

## The crux, adjudicated step by step

### Q1(a) — does module-case generic freeness fire on `O(Mat^{=r}) → O(Z_0)`? **NO (crisp).**

`GenericFreeness` rung-1 is the MODULE case: `Module.exists_free_localizedModule_of_isDomain` requires
`[Module.Finite R M]` (read in full, `GenericFreeness.lean:75,80`). Its own docstring is explicit
(`:27-31`): *"the full Grothendieck statement for a finitely-generated R-ALGEBRA B (relative dimension
possibly positive, e.g. B = R[X]) is a strictly stronger theorem (EGA IV 6.9.1, by Noether
normalization on top of dévissage) and is NOT covered here."* The map `O(Mat^{=r}) → O(Z_0)` is
finite-type-as-ALGEBRA with relative dimension `dim F_0 > 0` generically — so `O(Z_0)` is NOT a finite
MODULE over `O(Mat^{=r})`, and the module theorem cannot fire. Codex (decorrelated) gives the identical
crisp NO with the identical reason. **FACT.**

### Q1(b)/Q2 — does closed-fibre homogeneity make the no-jump free? **NO.**

The homogeneity (H transitive on `Mat^{=r}`, `mult` equivariant, all rank-`r` CLOSED fibres
H-isomorphic) proves `∀ y ∈ Mat^{=r}(k), (Z_0)_y ≅ (Z_0)_E`, so all CLOSED fibres have dim `dim F_0`.
But `relative_trdeg = trdeg_{K(Mat^{=r})} K(Z_0)` is the dimension of the GENERIC fibre — over `Spec
K(Mat^{=r})`, NOT a `k`-point. The generic fibre is *not literally* an H-translate of a closed fibre
(the H-action moves `k`-points among themselves, never to the generic point). Equating
generic-fibre-dim with closed-fibre-dim is the no-jump / upper-semicontinuity content, and the
homogeneity does not bridge it without one of:
1. a general fibre-dimension / generic-flatness theorem (the algebra-case wall), or
2. an explicit local trivialization (Q3).
There is NO Mathlib v4.29 "transitive equivariant morphism ⟹ generic fibre dim = closed fibre dim"
homogeneous-space lemma (searched — only `IsStandardSmoothOfRelativeDimension` exists, not a
fibre-dimension transport). Codex independently confirms: *"the generic fibre is over Spec
K(Mat^{=r}), not over a k-point, so it is not literally obtained by translating E."* **FACT / strong
INFERENCE on the Mathlib absence.**

### Q3 — does the gauge-trivialization make the no-jump free? **YES algebraically, but it is the same content as the direct route + a custom trdeg lemma; it does NOT shorten anything.**

The clean dodge: if `Z_0|_U ≅ U × F_0` (gauge trivialization on a dense chart `U = {detΔ≠0}`,
the regular section `A ↦ (mult A, P(mult A)•A)`), then `K(Z_0) ≅ K(Mat^{=r})(F_0)` and
`trdeg_{K(Mat^{=r})} K(Z_0) = trdeg_k K(F_0) = dim F_0` — IMMEDIATE, no semicontinuity, no
algebra-case generic freeness. **BUT:**
- The trdeg substrate IS present at v4.29 (verified): `MvPolynomial.trdeg_of_isDomain`
  (`TranscendenceBasis.lean:446`, `trdeg S (MvPolynomial ι S) = #ι`), `AlgEquiv.trdeg_eq`
  (`AlgebraicIndependent/Basic.lean:360`), `trdeg_add_eq` (`TranscendenceBasis.lean:548`,
  `[NoZeroDivisors A]`), `trdeg_eq_zero` — the engine already chains exactly these in
  `AffineNoetherRank.trdeg_eq_of_integral_injective`.
- The PRODUCT/base-change trdeg lemma (`trdeg_K(K ⊗_k A) = trdeg_k A`, or the fraction-field version
  needed to go from `K(Z_0) ≅ K(Mat^{=r})(F_0)` to `relative_trdeg = dim F_0`) is **NOT packaged** at
  v4.29 — must be assembled from the API (~1-2 modules). Codex confirms: *"I did not find a packaged
  product/base-change trdeg lemma … Q3 is mathematically the right dodge, but in Lean it still costs a
  small custom algebra layer."*
- **DECISIVE:** Q3 needs the gauge-trivialization `Z_0|_U ≅ U × F_0` as INPUT. That trivialization is
  EXACTLY the chart-trivialization of my prior fibration-dim design (Steps 2-4 there). And **once you
  have it, you do NOT need the trdeg-tower at all** — `dim Z_0 = δ + dim F_0` reads directly off
  `MvPolynomial.ringKrullDim_of_isNoetherianRing` (`KrullDimension/Polynomial.lean:119`, domain-free,
  reducible-OK) applied to `O(F_0)[δ vars]_{detΔ}`. So the trdeg-tower (and the irreducible-component
  reduction it required) is pure overhead: it forces `Z_0` irreducible to get a domain, but the direct
  route handles the reducible `F`/`Σ^r` natively via the Noetherian-only Krull-dim lemma and never
  needs a domain. **The trdeg-tower buys nothing.** INFERENCE (load-bearing), corroborated by Codex's
  framing that Q3 is "the clean dodge" but "not a v4.29 one-liner" and re-imports the chart iso.

---

## Component-reduction + max-over-union (steps 1-3 of the brief) — confirmed reachable, but overhead

- **`closure(H·F_0)` irreducible + dominant:** reachable from landed pieces. `H·F_0` = continuous
  (regular) image of the irreducible `H × F_0` (H irreducible as a product of `GL`s; `F_0` irreducible
  as a component), hence irreducible; its closure `repClosure` is irreducible (`OrbitClosure` has the
  `repClosure` machinery, `repClosure_mono`/`_idem`/transport). Dominance of `mult|_{Z_0}` onto
  `Mat^{=r}`: H transitive on `Mat^{=r}` (`exists_baseChange_of_rank_eq` + `mult_smul`), so the image
  contains the H-orbit of `mult(F_0-point) = E`, which is all of `Mat^{=r}`. ~1-2 modules. LANDED-reuse.
- **`F_0` a TOP component of F ⟹ `Z_0` a top component of `Σ^r` (dimensions line up):** `dim Z_0 = δ +
  dim F_0 = δ + dim F` (F_0 top ⟹ `dim F_0 = dim F`), and every top component of `Σ^r` is the H-sweep
  closure of a top component of `F` (the sweep `Σ^r = ⋃_P P·F` ⟹ each `Σ^r`-component is `H · (some
  F-component)`-closure). So `varietyDim Σ^r = max_i (δ + dim F_i) = δ + max_i dim F_i = δ + dim F =
  dim Z_0`. ~2-3 modules via `RadicalCatenary` (`dim = card − height`, max-over-minimal-primes) +
  `SigmaComponents` minimal-prime template. Reachable, as the brief flagged — but this whole layer is
  ABSENT from the direct chart-trivialization route (which glues charts, not components).

**`RadicalCatenary` max-over-union confirmed:** `height_add_ringKrullDim_quotient_eq_card_of_ne_top`
gives `varietyDim = card − height I` for any reducible `I`, and `height I = min_p height p` over
minimal primes ⟹ `varietyDim = max_p coheight p = max over components`. Clean, ~2-3 modules. **But it
is overhead the direct route avoids.**

---

## Stacks 030H verification (the brief asked: confirm present, exact name + hypotheses)

**CONFIRMED PRESENT at v4.29.** `Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis`, line 548:
```
@[stacks 030H] theorem trdeg_add_eq [Nontrivial R] {A : Type v} [CommRing A] [NoZeroDivisors A]
    [Algebra R A] [Algebra S A] [FaithfulSMul R S] [FaithfulSMul S A] [IsScalarTower R S A] :
    trdeg R S + trdeg S A = trdeg R A
```
Hypotheses: `R` nontrivial, **`A` (the top ring) has `NoZeroDivisors`** (= the domain requirement that
forces the irreducible-component reduction), the two `FaithfulSMul`s (faithful flatness of the tower
maps, = injectivity of the structure maps), and `IsScalarTower R S A`. The engine already invokes it
(`AffineNoetherRank.trdeg_eq_of_integral_injective`, `:52`), so the wiring pattern is proven. **FACT.**

---

## The full module decomposition (irreducible-bypass-via-trdeg-tower, as the brief specified)

| # | Step | Status |
|---|---|---|
| 1 | `F_0` a top component of `F`; `dim F_0 = dim F = varietyDim F` | MUST-BUILD ~1 mod (minimal-prime selection, `SigmaComponents` template) |
| 2 | `Z_0 = repClosure(H·F_0)` irreducible (⟹ `O(Z_0)` domain) | LANDED-reuse `OrbitClosure` + irreducible-image; ~1 mod |
| 3 | `mult|_{Z_0}` dominant onto `Mat^{=r}` (H transitive) | LANDED-reuse `exists_baseChange_of_rank_eq`+`mult_smul`; ~1 mod |
| 4 | **Gauge trivialization `Z_0|_U ≅ U × F_0`** (THE irreducible content) | MUST-BUILD ~3-4 mod (landed `endpointGauge`,`schurComplement_normal_form`,`mult_smul`; the set-iso→AlgEquiv plumbing) |
| 5 | `K(Z_0) ≅ K(Mat^{=r})(F_0)` ⟹ `relative_trdeg = dim F_0` (the no-jump) | MUST-BUILD ~1-2 mod: custom product/base-change trdeg lemma (substrate present, not packaged) |
| 6 | `trdeg_add_eq` wiring: `dim Z_0 = δ + dim F_0` | Mathlib-present `trdeg_add_eq` + landed transports; ~1 mod — **REDUNDANT given step 4** |
| 7 | `varietyDim Σ^r = max-over-components = dim Z_0` | MUST-BUILD ~2-3 mod (`RadicalCatenary` + `SigmaComponents`) |
| 8 | Assemble `hSweep` → `RouteCAssembly._of_sweep'` | LANDED; ~1 mod |

**Total ~9-11 modules.** Compare the DIRECT gauge-trivialization (no steps 1-3,5,6,7-as-components):
~7 modules (steps 4 + chart `+δ` via `ringKrullDim_of_isNoetherianRing` + chart-cover glue + assemble).
**The bypass is strictly heavier** because step 4 (the trivialization) is common, and the bypass adds
the component reduction (1-3,7) and the redundant trdeg layer (5-6) on top.

---

## Single biggest risk

**Step 4 — the gauge-trivialization `Z_0|_U ≅ U × F_0` as a coordinate-ring `AlgEquiv` (the set-iso →
regular-iso → AlgEquiv plumbing for the principal open).** This is the SAME risk flagged in the
fibration-dim design: if the localized-coordinate bridge gets messy it drifts toward the R2-3b-4 ring
plumbing. It is unavoidable in BOTH routes (it is the irreducible content of `hSweep`). The bypass adds
a SECOND risk the direct route lacks: **step 5's custom product/base-change trdeg lemma**
(`trdeg_K(K(Z_0)) = dim F_0` from the trivialization) — not packaged at v4.29, must be assembled, and
its correctness hinges on the fraction-field identification `K(U × F_0) = K(U)(F_0)` being clean. Since
step 6 (trdeg-tower) is redundant once step 4 lands, **building step 5 is wasted effort** — the
operator should drop the trdeg framing and take `dim Z_0 = δ + dim F_0` from
`ringKrullDim_of_isNoetherianRing` directly.

---

## Engine + Mathlib handles VERIFIED (file + name)

LANDED / Mathlib-present (read, confirmed):
- `GenericFreeness.{exists_free_localizedModule_of_isDomain (:80), exists_flat_localizedModule_of_isDomain
  (:89)}` — MODULE case only; `[Module.Finite R M]`. Docstring (`:27-31`) explicitly excludes the
  algebra case (EGA IV 6.9.1). **The crux: this does NOT cover the no-jump.**
- `trdeg_add_eq` (`TranscendenceBasis.lean:548`, `[NoZeroDivisors A]`) — Stacks 030H, PRESENT.
- `MvPolynomial.trdeg_of_isDomain` (`TranscendenceBasis.lean:446`), `AlgEquiv.trdeg_eq`
  (`AlgebraicIndependent/Basic.lean:360`), `trdeg_eq_zero` (`Transcendental.lean:80`) — the trdeg API
  the bypass's step 5 assembles from; the product/base-change combiner is NOT packaged.
- `MvPolynomial.ringKrullDim_of_isNoetherianRing` (`KrullDimension/Polynomial.lean:119`) — domain-free
  `+δ`; **makes the trdeg-tower redundant once the trivialization lands.**
- `OrbitClosure.{repClosure, repClosure_mono, repClosure_idem, repClosure_subset_of_subset_repClosure}`
  — irreducibility/closure of `Z_0`.
- `FibreNormalForm.{mult_smul (:77), exists_baseChange_of_rank_eq (:279)}` — H-equivariance + transitivity.
- `SchurGauge.{schurComplement_normal_form (:168), endpointGauge (:132)}` — the gauge for step 4.
- `RadicalCatenary.height_add_ringKrullDim_quotient_eq_card_of_ne_top` + `SigmaComponents`
  `minimalPrimes_sInf_of_finite_of_isPrime` — max-over-components (step 7).
- `RouteCAssembly.codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep'` (`:102`) — consumes `hSweep`.

SEARCHED AND ABSENT:
- Generic-freeness ALGEBRA case / relative Noether normalization over a domain (EGA IV 6.9.1) — the
  wall the CLOSED-fibre route hits.
- "Transitive equivariant morphism ⟹ generic fibre dim = closed fibre dim" homogeneous-space lemma.
- Packaged product/base-change trdeg `trdeg_K(K ⊗_k A) = trdeg_k A` (only the building blocks present).

---

## Decorrelated Codex (xhigh, gpt-5.x) — independent read

Fired with hypothesis WITHHELD (the three questions + facts; I did NOT tell it my "trdeg-tower is
redundant" conclusion). Codex CRUX VERDICT independently matches: *"no-jump WALLS for the closed-fibre
route: module generic freeness does not apply, and closed-fibre homogeneity alone does not identify the
generic fibre. It is avoidable only by proving an explicit gauge/birational trivialization; that does
not need algebra-case generic freeness, but the required product/base-change trdeg lemma is not
packaged in Mathlib v4.29."* On Q1(a) identical crisp NO; on Q1(b)/Q2 identical (generic fibre over
`Spec K`, not a `k`-point); on Q3 identical (trivialization is the clean dodge, trdeg substrate present
but the product/base-change combiner must be assembled). Transcript: `codex/no-jump-residual-{prompt,
answer}.md`. **Agree** on every load-bearing point. The one judgment I add beyond Codex: once the
trivialization (step 4) lands, the trdeg-tower (steps 5-6) is REDUNDANT — read `dim Z_0 = δ + dim F_0`
straight from `ringKrullDim_of_isNoetherianRing` — so the bypass is strictly heavier than the direct
chart-trivialization, and the recommendation is to build the latter.

---

## Close

- **Firmest result:** the no-jump residual `relative_trdeg = dim F_0` is NOT reachable from the landed
  module-case generic freeness, and closed-fibre homogeneity does not bridge generic-vs-special. The
  closed-fibre trdeg-tour WALLS (algebra-case generic freeness, ~12-20). The gauge-trivialization makes
  it reachable WITHOUT that wall, but the trivialization IS the irreducible content of `hSweep`, and
  once it is built the trdeg-tower adds nothing — so the irreducible bypass collapses to the **direct
  chart-trivialization route (~7 modules)** plus redundant component/trdeg overhead (~9-11 total).
  **Build the direct ~7-module trivialization; do not pursue the trdeg-tour.**
- **Most likely to break it:** the gauge-trivialization → coordinate-ring `AlgEquiv` plumbing (step 4),
  common to both routes — the same R2-3b-4-drift risk. De-risk with the SPECIFY I named in the
  fibration-dim design (pin `O(Σ^r ∩ U_Δ) ≅ O(FibreAlg)[δ free vars]_{detΔ}`, confirm δ vars free).
- **Next construction/consult to settle the open part:** that step-4 SPECIFY is the single highest-value
  de-risk for EITHER route. It is the bottleneck; the component-reduction and trdeg layers are
  avoidable overhead. The operator's build-vs-bank decision should be made against the **~7-module
  direct trivialization** number (not the ~12-20 walled trdeg-tour, and not the ~9-11 heavier bypass).
