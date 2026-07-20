# Thread P2.0 — de-`Tuple` feasibility probe (the Phase-2 gate)

Scout reconnaissance. LONGLIST → TRIAGE → read the squeeze → classify coupling → scratch-elaborate
the abstract keystone → Codex → VERDICT.

## What the squeeze is, file by file (read 2026-06-30)

```
varietyDim 𝒪  =  trdeg  ≤  genericDifferentialRank  ≤  finrank(range δ⁰)  ≤  finrank(cotangent)  =  varietyDim 𝒪
   └────────────── A4 (submersion, ≤) ──────────────┘      └────────── A6.1 (reverse, ≥) ──────────┘
```

- bottom-of-squeeze (A4, `≤`): `OrbitPullbackDim` (A0: varietyDim = ringKrullDim(range μ*)), `AffineNoetherRank`
  (A4.1: ringKrullDim = trdeg), `OrbitImageDim` (A4.4 assembly + A4.2 criterion discharge),
  `OrbitDifferentialRank` (A4.3 keystone: genericDiffRank ≤ finrank(range δ⁰)).
- top-of-squeeze (A6.1, `≥`): `OrbitSmooth` (L3: smooth at normal-form point), `OrbitTangentCotangent`
  (R2★…R6: range δ⁰ ↪ cotangent, finrank cotangent = varietyDim), `OrbitDifferential` (dμ_e = δ⁰, dual-number).
- headline: `VoigtDischarge` (le_antisymm → varietyDim = finrank(range δ⁰) → L7 → hVoigt).
- carrier: `OrbitVariety` (orbit-as-image irreducibility, `groupRing`/`genericUnit`/`orbitPullback`, ker μ* prime).

## Coupling classification (the deliverable's item 1)

(i) genuinely abstract — already DLN-free, `Tuple` only instantiates:
  - `genericDifferentialRank k B f` (B a k-domain, f : ι → B). Phase-1, `GenericRank.lean`. NO Tuple.
  - `trdeg_adjoin_le_genericDifferentialRank` (the A4.2 trdeg wrapper). Phase-1 `Trdeg.lean`. NO Tuple.
  - `DiffIndepCriterion` + `diffIndepCriterion_proof` (char-0 core). Phase-1. NO Tuple.
  - matrix-Kähler gate `derivMatrix_mul_apply`/`derivMatrix_inv_apply` (general `Derivation R A M`). Phase-1
    `Derivation/Matrix.lean`. NO Tuple.
  - base-change rank `finrank_range_baseChange` (general k, V, W). Phase-1 `LinearAlgebra/BaseChange.lean`.
  - `varietyDim Z` (Z : Set (σ → k), any σ). `Dimension/Codimension.lean`. NO Tuple.
  - ringKrullDim = trdeg for an fg k-domain (`ringKrullDim_quotient_unbotD_eq_trdeg_toNat`). `Dimension/Localization`.
  - the M3 smooth⟹regular cotangent brick `finrank_cotangentSpace_eq_of_isSmoothAt` + `Dimension/{Regular,Smooth}`
    + `CotangentLocalization` (general k-algebra A, maximal m). NO Tuple.
  - `traceEquiv`/`traceFun`/`finrank_range_deltaT` already stated for ARBITRARY `{ι}[Fintype ι]{a b : ι→ℕ}` —
    matrix-shape products, NOT `Tuple`/`cochain`-specific (only need finite index + shape fns). Confirmed by
    scratch Q2 elaborating with a bare `{ι}{a b}`.
  - `finrank_range_dualMap_eq_finrank_range` (the deep transpose-rank fact) is MATHLIB's, any `f : V₁ →ₗ[K] V₂`.

(ii) mechanically de-`Tuple`-able — incidental encoding, rename/parameterize frees it:
  - `groupRing d` / `genericUnit` / `genericUnitInv` / `genericFactor` / `genericOrbitCoord` / `orbitPullback`
    (`OrbitVariety`): all expressed over `GroupCoord d` / `RepCoord d` (sigma of Fin-matrix coords). The
    *constructions* (Localization.Away of a det product; aeval of a coordinate family) are generic; the
    matrix-tuple is the chosen presentation. Parameterizing on (group coord ring R, orbit family f : ρ → R)
    frees them. `orbitMap`/`orbitSet`/`range_orbitMap`/`vanishingIdeal_range_orbitMap_eq_ker`/
    `isPrime_vanishingIdeal_orbitSet` (orbit-as-image irreducibility) only use: an irreducible domain R as
    coordinate ring + an aeval pullback; the `MvPolynomial.funext`-over-infinite-domain `⊆` is generic.
  - A0/A4.1/A4.4 assembly (`OrbitPullbackDim`/`AffineNoetherRank`/`OrbitImageDim`): orbit specialisations
    transported through the first-iso `quotientKerEquivRangeOrbitPullback`; the general facts live one layer
    down. De-Tuple = re-state on (R, f) + the L6.4 ideal-equality hypothesis (orbitRankLocus = orbitSet — that
    box-move equality STAYS DLN-local, supplied as a hypothesis to the abstract A0).
  - `OrbitSmooth` L3.0–L3.4: the G_d-automorphism / dense-orbit / smooth-point-transport argument. The
    *structure* (a group acting on the coord ring by k-algebra automorphisms, with a dense orbit, generic
    smoothness density of a perfect field) is generic; the matrix-tuple supplies the concrete G-action
    `baseChangePullback P` and the density `vanishingIdeal_orbitSpecSet_eq_bot`. Abstract hypothesis: "a group
    of k-algebra automorphisms of R/I with a dense orbit of k-rational points."
  - `OrbitTangentCotangent` R3–R6 (descend dirDeriv to A, cotangent functional, finrank cotangent = varietyDim):
    generic once you have the orbit ideal I prime + a smooth k-rational point + a directional-derivative
    derivation killing I. `residueFieldNormalFormEquiv` (k-rational point) is generic (surjective eval).

(iii) irreducibly `Tuple`-shaped — the argument USES the matrix-tuple structure essentially:
  CANDIDATES (the spots to scrutinise, all in two lemmas):
  - `D_orbit_conj` (`OrbitDifferentialRank` step b): D(f_x) = Σ (V₂)_{sa}(V₁⁻¹)_{bt} • bracketG(mcΘ). This
    USES that the orbit coordinate is the *conjugation* `V₂ · F · V₁⁻¹` of a constant by group elements, and
    the Maurer–Cartan factorisation D(f_x) = bracket of V⁻¹DV. NOT a property of a generic orbit map.
  - `pair_deltaT_eq_pair_deformationδ` + `orbitAction_eps_eq_deformationδ` (`OrbitDifferential` R2★ certificate):
    the entrywise `δ⁰`-bracket structure (`φ_{i+1} M_i − M_i φ_i`) with Fin.succ/castSucc casts.

  RESOLUTION (why these are (ii)-with-an-abstract-hypothesis, NOT a (iii) HALT): see "the crux" below.

## The crux: is `D_orbit_conj` + the adjoint pairing irreducibly Tuple-shaped?

The honest content of (b)+(c) is the geometric identity **"the differential of the orbit map at the point
factors through the infinitesimal (Lie-algebra) action δ⁰."** In the matrix-tuple case δ⁰ is the quiver
coboundary and the factorisation is the Maurer–Cartan conjugation identity. But the SQUEEZE only consumes the
*consequence*: `span_K {D(f_x)} ≤ range_K(δ⁰.baseChange K)` composed with an adjoint carrier — i.e.
`genericDifferentialRank ≤ finrank(range δ⁰)`. That consequence is exactly the abstract keystone signature,
which scratch-elaborates (Q3) with NO cochain/Tuple. So the matrix-tuple structure is needed to *DISCHARGE*
the factorisation hypothesis for the DLN instance — it is not needed to *STATE* the abstract engine. The
adjoint/trace step (c) reduces to Mathlib's `finrank_range_dualMap_eq_finrank_range`: any finite-dim δ⁰ has
`finrank(range δ⁰.dualMap) = finrank(range δ⁰)`; `deltaT` is merely the transport of `δ⁰.dualMap` across the
chosen self-dualities — confined to one file, consumed nowhere else. Drop `deltaT`, keep `δ⁰.dualMap`, and (c)
is generic.

CONCLUSION (pre-Codex): the irreducibly-matrix content is the *discharge of one hypothesis* (the
Maurer–Cartan factorisation `span {D(f_x)} ≤ range(adjoint ∘ δ⁰.baseChange)`), which the abstract engine takes
as input and the DLN instance proves. That is the textbook (ii) pattern: abstract the statement, instance
discharges the hypothesis. ⇒ leaning PROCEED.

## Scratch elaboration (uncommitted, `scratch_p20_probe.lean`)

Q1 (genericDifferentialRank abstract on (R,f)) ✅ elaborates.
Q2 (traceEquiv at bare `{ι}{a b}`, no Tuple) ✅ elaborates.
Q3 (abstract A4.3 keystone signature: `genericDifferentialRank k R f ≤ finrank k (range δ)` for abstract
   `δ : C0 →ₗ[k] C1` finite-dim, hypothesis `span{D(f_x)} ≤ range(L ∘ δ.baseChange K)`) ✅ elaborates,
   body `sorry` (scratch only) — only the `sorry` warning, no type errors. NO cochain/Tuple in the statement.

=> the core feasibility signal is POSITIVE: the keystone restates cleanly against the abstract interface.

## Codex (decorrelated, xhigh) — CONVERGES on PROCEED

Artefact: `codex/de-tuple-verdict-{prompt,answer}.md`. Codex's verdict matches the pre-Codex analysis
and SHARPENS it:
- PROCEED, but the abstraction is valid only as a **hypothesis-carrying** engine: the two geometric facts
  (Maurer–Cartan differential factorisation; infinitesimal-action / δ⁰φ-kills-ideal) are INPUTS the
  matrix-tuple instance discharges — NOT consequences of a bare `aeval genericOrbitCoord`.
- Step (b) D_orbit_conj: the abstract content is the group-action identity `dμ_g = d(g·−)_M ∘ dμ_e ∘ dL_g⁻¹`
  (dually: `D(orbit coords) factors through (dμ_e)*`). General for a smooth algebraic group action, but not
  free from `μ* = aeval`. Package as the hypothesis `span_K{D(fρ)} ≤ range(L ∘ δAdj.baseChange K)`.
- Step (c) deltaT/trace: NOT Tuple-essential — `finrank range(δ⁰.dualMap) = finrank range δ⁰`
  (`LinearMap.finrank_range_dualMap_eq_finrank_range`, Mathlib). `traceEquiv` is the matrix instance.
- Smooth side: interface-shaped but needs explicit hyps; over non-alg-closed k, "dense orbit" must mean
  enough k-orbit points to meet the smooth locus (or assume the smooth k-rational base point directly).
- Recommended boundary: a SMALL abstract engine (`GenericRankBound`, `AdjointRank`, `CotangentInjection`,
  `SmoothCotangentDim`), NOT a full algebraic-group framework.

My scratch Q3/keystone-`example` already used exactly this hypothesis shape (`hMC`/`hspan`), independently
confirming the feasibility before reading Codex.

## VERDICT: PROCEED (hypothesis-carrying small engine). Rung plan in report.md.

