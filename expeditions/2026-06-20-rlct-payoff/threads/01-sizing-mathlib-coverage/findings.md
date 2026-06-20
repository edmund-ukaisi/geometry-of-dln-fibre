# Thread 01 — sizing Mathlib coverage (scout)

Recon for the `rlct-payoff` expedition: the Mathlib + in-engine coverage that gates **Half A**
(`Σ^r` geometry + irreducible components + `θ`) and **Half R** (the RLCT / SLT payoff). Read-only on
committed `.lean`; signatures pinned by compiling `#check` against Mathlib `v4.29.0`
(`lean/.lake/packages/mathlib`). Decorrelated Codex (xhigh) consult: `codex/feasibility-{prompt,answer}.md`.

## TL;DR — two verdicts

- **Half A is BOUNDED / buildable in-expedition.** Mathlib carries the full
  `minimalPrimes ≃o irreducibleComponents` bridge, `Ideal.height = ⨅ minimalPrimes primeHeight`
  (codim-of-union = min-over-components, **definitionally**), and the finite-cover irreducibility brick.
  The engine already defines `Σ^r` (`productRankLocus`), its closure `c̄Σ^r` (`productRankLocusLE`),
  `mult`, the fibre, the per-orbit `Ō_M = orbitRankLocus M` (irreducible + prime), and the per-orbit
  geometric codim. **No components sub-library is needed.** The build is an *assembly*, not a foundation.
- **Half R is a SCOPE-SURPRISE → surface.** Mathlib has **zero** RLCT / SLT / log-canonical-threshold /
  Igusa-zeta / resolution-of-singularities / Newton-polyhedron scaffolding. A from-scratch analytic RLCT
  *value* proof (Aoyagi/Watanabe) is multi-month and out of expedition scope. The honest route is a
  **Cited/interfaced rlct**: `rlct(K^DLN_B) = C/2` against an interface carrying the cited
  `rlct ≤ codim/2` bound + the Aoyagi value — with **no `sorry`-free in-engine proof of the analytic value**.
- **A confound to surface (refutes a brief premise): `θ ≠ rlcm`.** The brief bundles `(C/2, θ)` as "the
  complete learning coefficient", reading `θ` (number of top-dim components) as the SLT multiplicity `m`.
  **The paper's own Remark (after Thm `thm:aoyagi-rlct`) states there is no simple relationship between
  the RLCT multiplicity `rlcm(K^DLN_B) = m²{S̃/m}(1−{S̃/m})` and the component count
  `k = C(m, S̃−m⌊S̃/m+½⌋)`.** So `θ` must be kept as a **geometric** component count, not smuggled in as
  the rlcm half of the payoff. (Codex independently agrees: Watanabe's multiplicity is the pole order /
  `log log n` coefficient, not the component count.)

---

## Half A — table (claim · Mathlib name or ABSENT · signature)

All `#check`s below type-checked against Mathlib v4.29.0 (scratch file, since deleted).

### A.1 Irreducible components / maximal-members

| Claim | Mathlib name | Signature (verified by `#check`) |
|---|---|---|
| `irreducibleComponents` of a space | `irreducibleComponents` | `(X) → [TopologicalSpace X] → Set (Set X)`, `= {s | Maximal IsIrreducible s}` |
| components = maximal closed-irreducibles | `irreducibleComponents_eq_maximals_closed` | `irreducibleComponents X = {s | Maximal (fun x => IsClosed x ∧ IsIrreducible x) s}` |
| **irreducible covered by finite closeds ⟹ in one** | `isIrreducible_iff_sUnion_isClosed` | `IsIrreducible s ↔ ∀ t : Finset (Set X), (∀ z ∈ t, IsClosed z) → s ⊆ ⋃₀ ↑t → ∃ z ∈ t, s ⊆ z` |
| a component inside a finite union of components is one of them | `mem_of_subset_sUnion_irreducibleComponents` | `Z ∈ irreducibleComponents X → ∀ S, S.Finite → S ⊆ irreducibleComponents X → Z ⊆ ⋃₀ S → Z ∈ S` |
| every irreducible sits in a component | `exists_mem_irreducibleComponents_subset_of_isIrreducible` | `IsIrreducible s → ∃ u ∈ irreducibleComponents X, s ⊆ u` |
| components are closed | `isClosed_of_mem_irreducibleComponents` | `s ∈ irreducibleComponents X → IsClosed s` |
| "components of a finite union of irreducible closeds = maximal members" (brief's named lemma) | **ABSENT as a single lemma** | derivable from the four rows above (the `isIrreducible_iff_sUnion_isClosed` route) |

### A.1 / A.3 The decisive bridge: `minimalPrimes ≃o irreducibleComponents`

| Claim | Mathlib name | Signature |
|---|---|---|
| min primes of `I` ↔ components of `zeroLocus I` | `Ideal.minimalPrimes.equivIrreducibleComponents` | `(I : Ideal R) → I.minimalPrimes ≃o (irreducibleComponents (zeroLocus I))ᵒᵈ` `[CommSemiring R]` |
| min primes of `R` ↔ components of `Spec R` | `minimalPrimes.equivIrreducibleComponents` | `minimalPrimes R ≃o (irreducibleComponents (PrimeSpectrum R))ᵒᵈ` |
| `vanishingIdeal '' components = minimalPrimes` | `vanishingIdeal_irreducibleComponents` | `PrimeSpectrum.vanishingIdeal '' irreducibleComponents (PrimeSpectrum R) = minimalPrimes R` |
| `zeroLocus '' minimalPrimes = components` | `zeroLocus_minimalPrimes` | `zeroLocus ∘ (↑) '' minimalPrimes R = irreducibleComponents (PrimeSpectrum R)` |
| `zeroLocus I` is a component ↔ `I.radical` minimal prime | `zeroLocus_ideal_mem_irreducibleComponents` | `zeroLocus I ∈ irreducibleComponents (Spec R) ↔ I.radical ∈ minimalPrimes R` |

### A.2 Variety-of-union / intersection (PrimeSpectrum side only)

| Claim | Mathlib name | Signature |
|---|---|---|
| `zeroLocus (I ⊓ J) = zeroLocus I ∪ zeroLocus J` | `PrimeSpectrum.zeroLocus_inf` | `zeroLocus ↑(I ⊓ J) = zeroLocus ↑I ∪ zeroLocus ↑J` |
| `zeroLocus (s ∪ s') = ∩` | `PrimeSpectrum.zeroLocus_union` | `zeroLocus (s ∪ s') = zeroLocus s ∩ zeroLocus s'` |
| `zeroLocus (⨆ I) = ⋂ zeroLocus` | `PrimeSpectrum.zeroLocus_iSup` | `zeroLocus ↑(⨆ i, I i) = ⋂ i, zeroLocus ↑(I i)` |
| union of zeroLoci = zeroLocus of `span ⊓ span` | `PrimeSpectrum.union_zeroLocus` | `zeroLocus s ∪ zeroLocus s' = zeroLocus ↑(span s ⊓ span s')` |
| **point-space** (`MvPolynomial.zeroLocus` on `σ → k`) union/inter/iSup/minimalPrimes | **ABSENT** | the engine's `Σ^r`/`Ō_M` live point-side; the union algebra exists only on `PrimeSpectrum` |

### A.3 Dimension / codim of components, top-dim selection

| Claim | Mathlib name | Signature |
|---|---|---|
| **codim = min over components** | `Ideal.height` | `I.height = ⨅ J ∈ I.minimalPrimes, primeHeight J` — holds **by `rfl`** (definitional) |
| prime height = order height in Spec | `Ideal.primeHeight` | `[I.IsPrime] → ℕ∞`, `= Order.height (⟨I,_⟩ : PrimeSpectrum R)` |
| height of a prime = its primeHeight | `Ideal.height_eq_primeHeight` | `[I.IsPrime] → I.height = I.primeHeight` |
| co-dimension (order) | `Order.coheight` | `[Preorder α] → α → ℕ∞` |
| Krull dim of a ring | `ringKrullDim` | `(R) → [CommSemiring R] → WithBot ℕ∞` |
| equidimensional / pure-dimensional predicate | **ABSENT** | not needed — `(2,2,2)` shows `c̄Σ^0` is NOT equidimensional (codims 4,4,3); `θ` filters to min-codim |

### In-engine bricks already LANDED (the substrate Half A consumes; `lean/DLNFibre/Core/`)

| Object / fact | Where | Form |
|---|---|---|
| `Σ^r = {rk(mult) = r}`, `c̄Σ^r = {rk ≤ r}`, `mult`, `fibre = mult⁻¹(B)` | `Setup.lean` | `productRankLocus`, `productRankLocusLE`, `mult`, `fibre` — **point-sets, defined** |
| `Ō_M = orbitRankLocus M` (Abeasis–Del Fra Thm 3.8) | `OrbitClosure.lean` | `image_orbitRankLocus_eq_repClosure_orbitSet` (set), `vanishingIdeal_orbitRankLocus_eq_orbitSet` (ideal), `[Infinite k]` |
| `Ō_M` irreducible (prime vanishing ideal) | `OrbitClosure.lean` | `isPrime_vanishingIdeal_orbitRankLocus` `[IsAlgClosed k]` |
| engine irreducibility predicate (point-side, via `pointToPoint` into Spec) | `NullstellensatzCodim.lean` | `IsZariskiIrreducible Z := IsIrreducible (pointToPoint '' Z)`; `…_iff_isPrime_vanishingIdeal` |
| geometric codim `= Ideal.height ∘ vanishingIdeal` | `OrbitCodim.lean` | `codimRep coord Z`, `codimRepCanonical Z` |
| per-orbit geometric codim `= orbitLinearCodim` (Voigt, proved) | `VoigtDischarge`/`CThetaGeometric.lean` | `codimRepCanonical_orbitRankLocus_eq_orbitLinearCodim` `[IsAlgClosed k][CharZero k]` |
| combinatorial `(C, θ)`: `cCodim`, `numTop` | `CTheta.lean` | `numTop = #{Kostant partitions attaining min codimForm}` |
| `cCodim = min over partitions of geometric orbit-closure codim` | `CThetaGeometric.lean` | `cCodim_eq_inf_geomCodim` (per-orbit; aggregate `Σ^r` reading **OPEN**, by its own roadmap §"remaining step") |
| `(2,2,2)`, r=0: `C=3`, `θ=1` (matches paper Ex: 3 comps, codims 4,4,3 ⟹ 1 top) | `CTheta.lean` | `cCodim_d222_zero=3`, `numTop_d222_zero=1` (kernel `decide`) |

---

## Half R — table

| Searched-for object | Mathlib status |
|---|---|
| `rlct`, `logCanonicalThreshold`, `Function.logCanonicalThreshold`, `realLogCanonicalThreshold` | **ABSENT** (all "unknown identifier" by `#check`) |
| `lct`, log-canonical threshold (complex) | **ABSENT** |
| Watanabe / singular learning / learning coefficient / free energy | **ABSENT** |
| Igusa / local zeta function of a polynomial / archimedean zeta `∫|F|^s` | **ABSENT** |
| resolution of singularities / Hironaka / blow-up / desingularisation | **ABSENT** |
| Newton polyhedron / Newton polygon | **ABSENT** |
| Hilbert–Samuel multiplicity / multiplicity of a variety | **ABSENT** |
| `Module.length` | PRESENT (`(R)(M) → … → ℕ∞`) — module length, **not** analytic multiplicity (does not help) |
| `MeasureTheory.integral`, `lintegral`, `Real.rpow` | PRESENT — the analytic *substrate* a from-scratch rlct ∫|F|^{-s} definition would need, but only the substrate |

**Paper facts (primary source, confirmed):**
- `rlct(F) := sup { s ∈ ℝ | |F|^{-s} locally integrable }` (Def `defn:rlct`) — purely analytic.
- Bound `rlct(F) ≤ codim F⁻¹(0) / 2` (eqn `rlct_upper_bound_glob`) — **Cited** (their Prop / Aoyagi / Watanabe), no in-paper proof.
- Thm `thm:aoyagi-rlct`: `rlct(K^DLN_B) = codim(mult⁻¹(B))/2`. The **proof is a notation translation**
  matching the engine's codim formula to Aoyagi [Thm 1]'s `λ` — the paper proves **no** independent
  analytic value; the value is Aoyagi's, cited.
- **`rlcm ≠ θ`** (Remark after the theorem): no simple relationship between the RLCT multiplicity and the
  irreducible-component count.

---

## Feasibility verdict

### Half A — **BOUNDED. Build it (an assembly, no sub-library).**

The components/codim arena is Mathlib's `PrimeSpectrum`, where every needed brick is present.
The engine carries `Σ^r`/`c̄Σ^r`/`mult`/`fibre`/`Ō_M` and the per-orbit irreducibility + geometric codim.
The Phase-G/θ work is to **assemble** these, not to found a theory:
- **G2** `c̄Σ^r = ⋃_{m: m_{0N} ≤ r} Ō_M` as a closed variety, with `vanishingIdeal(c̄Σ^r) = ⋂_M vanishingIdeal(Ō_M)`.
- **G3** components of `c̄Σ^r` = maximal `Ō_M` ↔ minimal primes of `vanishingIdeal(c̄Σ^r)` (Mathlib `equivIrreducibleComponents`).
- **θ** top-dim component = min-`primeHeight` minimal prime; `θ = numTop` = their count (via `Ideal.height = ⨅ primeHeight` + the engine's per-orbit codim = `codimForm`).

**Architecture (Codex's refinement — adopt):** define the closed locus **directly on `PrimeSpectrum` by
its ideal** `I_{≤r} := ⨅_{m: m_{0N}≤r} vanishingIdeal(Ō_M)` (or radical of the rank-minor ideal), do all
component-counting there, and keep the point-space (`Tuple d`) ↔ `PrimeSpectrum` correspondence a **thin
comparison layer** (it is needed because `codimRep`/the engine live point-side, but the union algebra is
Spec-side). Fighting the union/intersection algebra on the point-space `MvPolynomial.zeroLocus` (ABSENT
there) is the trap to avoid.

**Single hardest must-build lemma (Half A):** the finite-family component theorem —
> for the finite family of prime orbit ideals `{vanishingIdeal(Ō_M) : m_{0N} ≤ r}`, the irreducible
> components of `zeroLocus(⨅ ideals)` are exactly the `zeroLocus` of the **inclusion-minimal** members
> (= maximal `Ō_M`), and `height(⨅ ideals) = min over the family of their heights`.

The first half is `equivIrreducibleComponents` + dropping non-minimal (non-maximal-closure) members; the
second is `Ideal.height`'s definition modulo "the minimal primes of `⨅ pᵢ` over a finite family of primes
are the minimal members" (Noetherian — `MvPolynomial (RepCoord d) k` is Noetherian; **verify** the exact
Mathlib lemma for `minimalPrimes (⨅ finite primes)`). Secondary but real: the point-space→Spec bridge
`vanishingIdeal(⋃ Ō_M) = ⋂ vanishingIdeal(Ō_M)` and that `c̄Σ^r` (rank locus) equals that union — the
engine has the per-orbit `vanishingIdeal_orbitRankLocus_eq_orbitSet`; the **aggregate** `c̄Σ^r = ⋃ Ō_M`
is the genuinely-new structural step (the paper's stratification Cor `cor:irred_comp`).

### Half R — **SCOPE-SURPRISE. Cited/interfaced rlct, not a sub-library. Surface to the operator.**

No definition-side scaffolding exists. Two honest options:
1. **Cited interface (recommended):** introduce the rlct as an *interface* — a structure / hypothesis
   bundling (i) the analytic definition's value abstractly and (ii) the cited bound `rlct ≤ codim/2`
   (Aoyagi/Watanabe, per project policy) — and state `rlct(K^DLN_B) = C/2` against it. The new content is
   `codim(mult⁻¹(B)) = C` (geometry, Half A); the analytic equality is Cited, named next to the claim.
   Cost: small (the interface + the codim plug-in). Honesty: the `rlct = …`-named result must denote
   "given the cited bound + Aoyagi value", never an unproved analytic theorem (the CLAUDE.md `rlct_…` trap).
2. **From-scratch analytic rlct DEFINITION only** (`rlct F := sSup {s | LocallyIntegrable |F|^{-s}}`):
   plausibly ~20–40 support lemmas for a clean *definition* (Codex estimate; needs Mathlib
   `LocallyIntegrable`/`IntegrableOn` APIs — **verify**), but proving the **value** `= C/2` needs
   normal-crossing / local-zeta / resolution machinery that is **absent** — multi-month, out of scope.
   So even option 2 ends at a *definition*; the value still routes through the cited bound.

Either way the analytic *value* is Cited. **The field bridge is a second hazard:** the engine is over
`[IsAlgClosed k][CharZero k]` (⊆ ℂ setting); rlct is real-analytic over ℝ. The interface must connect only
to the **algebraic/combinatorial codim value `C`** (which the paper's `thm:base_field` makes field-robust),
not pretend the ℂ-geometry is the ℝ-analysis.

**Single hardest must-build "lemma" (Half R):** the cited-interface theorem
`rlct(K^DLN_B) = codim(mult⁻¹(B))/2 = C/2`, with the right normalisation and **no multiplicity claim**.
From scratch, the unreachable lemma is the normal-crossing / local-integrability criterion for the value.

### Recommended scoping

- **Phase G + θ: pursue (P1).** Define `c̄Σ^r` on `PrimeSpectrum`; prove G2 (`= ⋃ Ō_M`), G3 (components =
  maximal `Ō_M` via `equivIrreducibleComponents`), `θ = numTop` (min-`primeHeight` count). Consume the
  LANDED per-orbit Voigt codim. This closes the `CThetaGeometric` "remaining step" roadmap and is the
  genuinely-new geometric content — fully in scope, zero-cited, `[IsAlgClosed k][CharZero k]`.
- **Phase D: pursue (cheap).** `Rep_d`/`mult`/`fibre` are defined; the square-Frobenius loss + identifying
  the loss landscape's zero-locus with `c̄Σ^r` is light glue (`DLNFibre.DLN`, currently a one-file stub).
- **Phase R: SURFACE before building.** Re-scope to a **Cited rlct interface** (`rlct = C/2`, multiplicity
  dropped), or accept a from-scratch *definition* with the value Cited. The operator decides grind vs
  interface. The `(C/2, θ)` "complete learning coefficient" framing must be corrected: **`θ` is the
  geometric top-component count, not the rlcm**; the payoff that is honestly reachable is
  `rlct = C/2` (Cited bound + Aoyagi value) **plus** `θ` as a separate geometric invariant.

### Brief premises to correct (for the controller's re-scope)
- "`m = θ`" / "`θ` is the multiplicity half of the very payoff" — **refuted by the paper's own remark.**
  Keep `θ` geometric.
- Paper main.tex writes `c̄Σ^r := {rk ≥ r}` (line 758) but calls it the Zariski closure of `{rk=r}`; the
  closure of `{rk=r}` is `{rk ≤ r}` (rank is lower-semicontinuous). The **digest** and the **engine**
  (`productRankLocusLE = {rk ≤ r}`) use the correct `≤`. Build against `{rk ≤ r}`; the paper's `≥` is a
  source typo/convention slip. **Confirm with the pen-and-paper math-sizing thread.**

## Kill-conditions checked
- *Half A bounded?* Kill if any of `equivIrreducibleComponents` / `height = ⨅ primeHeight` /
  `isIrreducible_iff_sUnion_isClosed` were absent → all PRESENT (`#check`).
- *Half R absent?* Kill if any `rlct`/`lct`/`Watanabe`/`Igusa`/`logCanonicalThreshold` existed → none do.
- *`θ = rlcm`?* Kill if the paper asserted the identity → the paper asserts the **negation**.
