# Thread 08 — Phase 2 recon: the real-AG route to PROVE `hT`

**Type:** scout (reconnaissance — map Mathlib + banked-Lean terrain, adjudicate the route, produce the
lemma ladder; decorrelated Codex). **No Lean written.** Output = route recommendation + lemma ladder +
cost/risk. All file refs are to the controller worktree `…/theta-components/lean` (the
`expedition/rlct-bridge` tree, authoritative for Phase 1+banked machinery).

## The target (pinned exactly)

`hT : codimRealFibre d B = codimRepCanonical (k:=K) (fibre K d (B.map ι))`
(`DLN/RlctPayoff.lean:447`, `[Field K][IsAlgClosed K][CharZero K]`, `ι : ℝ→+*K`).
`codimRealFibre := codimRepCanonical (k:=ℝ)` (`RlctPayoff.lean:317`).

**Banked reduction** `codimRealFibre_eq_codimRepCanonical_of_dimTransfer` (`RlctPayoff.lean:404`):
given both fibres nonempty + the atomic **dim-transfer `T′`**

> `varietyDim (canonicalCoord d '' (fibre ℝ d B)) = varietyDim (canonicalCoord d '' (fibre K d (B.map ι)))`

it PROVES `hT` via the field-generic catenary. **So Phase 2's whole job is `T′`** — and `varietyDim_ℝ ≤
varietyDim_K` is NOT the relevant split here: the cleaner finding (below) is that BOTH sides equal one
field-independent integer-matrix rank, so the squeeze gives equality directly without an inequality pair.

---

## HEADLINE FINDING — thread 07's "(a) dim/trdeg route ABSENT" is SUPERSEDED

Thread 07 (verdict iii: "T cited, not bounded-provable") was **right that the real-radical / real-
Nullstellensatz / semialgebraic-dim route is absent**, and right that a naive `vanishingIdeal`
base-change is the `x²+y²` trap. But it **missed that the repo already banks the entire orbit-dimension
computation as a FIELD-GENERIC algebraic squeeze that never touches the real radical**:

> `varietyDim_k(orbit closure) = finrank_k (range δ⁰_M)` — a squeeze of two inequalities, of which the
> `≤` is already proved over any `[CharZero k][Infinite k]` (holds over ℝ) and the `≥` is proved over
> `[IsAlgClosed k]` but its proof uses alg-closedness **only to obtain `PerfectField k`** (ℝ qualifies).

`finrank_k (range δ⁰_M)` is the rank of a FIXED integer (0/1-entry) matrix depending only on the
combinatorial `M = realizerD` — invariant under any char-0 field extension. So `varietyDim_ℝ(orbit) =
finrank_ℝ(range δ⁰) = finrank_K(range δ⁰) = varietyDim_K(orbit)`, **purely algebraically, local at the
rational point `M`, with no real-IFT and no density argument**. Decorrelated Codex (xhigh) reached the
same verdict independently — Route 1 (squeeze), `IsAlgClosed → PerfectField` is the clean route; Route 2
(ℚ-unirationality density) is correct but needs absent Mathlib infra. (`codex/realag-route-answer.md`.)

The earlier "needs a smooth full-dim real point per top component + real-density⟹dim" framing was the
analytic *reason* the dims coincide; the LEAN route does not formalise that reason — it computes both
dims as the same `finrank(range δ⁰)` and the smooth-real-point fact enters only as the LOCAL
`varietyDim_ℝ = ringKrullDim(local ring at M)` equidimensionality, which is field-generic.

---

## Deliverable 1 — Mathlib v4.29 + banked-repo inventory (the crux pieces, EXACT names)

### Route 1 (squeeze via δ⁰) — what EXISTS (banked, verified names)

| piece | name + location | field hyp | status |
|---|---|---|---|
| catenary `height + varietyDim = card` (bedrock, prime ideal) | `height_vanishingIdeal_add_varietyDim_eq_card` `NullstellensatzCodim.lean:147` | `[Finite σ]` only | **field-generic** ✓ |
| catenary on `codimRepCanonical`/fibre | `RadicalCatenary.codimRepCanonical_add_varietyDim_eq_card_of_nonempty` `RadicalCatenary.lean:179` | any `[Field k]`, nonempty Z | **field-generic** ✓ (used by the banked reduction) |
| `varietyDim(orbit) = ringKrullDim(orbitPullback.range)` (A0) | `varietyDim_eq_ringKrullDim_range_orbitPullback` `OrbitPullbackDim.lean:74` | `[Infinite k]` | **field-generic** ✓ |
| `varietyDim(orbit) ≤ finrank(range δ⁰)` (A4 submersion, unconditional) | `varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional` `OrbitDifferentialRank.lean:664` | `[CharZero k][Infinite k]` | **holds over ℝ** ✓ |
| trdeg ≤ generic differential rank (char-0 Jacobi–Zariski core) | `trdeg_adjoin_le_genericDifferentialRank` `JacobianTrdeg.lean:201`; `diffIndepCriterion_proof` `:118` | `[CharZero k]` | **holds over ℝ** ✓ |
| `finrank(range δ⁰) ≤ varietyDim(orbit)` (A6.1 reverse — **THE CRUX**) | `finrank_range_deformationδ_le_varietyDim` `OrbitTangentCotangent.lean:641` | `[IsAlgClosed k]` (declared) | **needs relax → `[PerfectField k]`** |
| smooth point ⟹ regular local, `finrank cotangent = dim` (M3) | `finrank_cotangentSpace_eq_of_isSmoothAt` `SmoothPointRegular.lean:198`; `smooth_point_isRegularLocalRing` `:167` | `[IsAlgClosed k]` (declared) | **PerfectField suffices** (in-file docstring `:21` says so) |
| local Krull dim at a smooth point = relative dim | `ringKrullDim_localizationAtPrime_eq_of_isSmoothAt` `SmoothLocalRelativeDimension.lean:113` | **`[Field k]` only** | **field-generic** ✓ (docstring: "alg closedness not used") |
| equidimensionality `m.height = ringKrullDim A` (finite-type domain, GAP3) | `ringKrullDim_localizationAtPrime_isMaximal_eq_fintype` `OrbitTangentCotangent.lean:87` | `[Field k]` only | **field-generic** ✓ |
| orbit smooth at rational point M | `isSmoothAt_normalFormIdeal` `OrbitSmooth.lean:506` ← `exists_orbitPointIdeal_isSmoothAt` `:487` | `[IsAlgClosed k]` (declared); proof uses `dense_smoothLocus_of_perfectField` + `dense_orbitSpecSet` | **PerfectField suffices** |
| orbit vanishing ideal prime (L1) | `isPrime_vanishingIdeal_orbitSet` `OrbitVariety.lean:372` | `[IsAlgClosed k]` (declared); proof = `RingHom.ker_isPrime` via `vanishingIdeal_range_orbitMap_eq_ker [Infinite k]` | **`[Infinite k]` suffices** (proof reads it) |
| `vanishingIdeal(orbitRankLocus) = vanishingIdeal(orbitSet)` | `vanishingIdeal_orbitRankLocus_eq_orbitSet` `OrbitClosure.lean:972` | `[Infinite k]` | **field-generic** ✓ |
| Mathlib generic smoothness | `Scheme.Hom.dense_smoothLocus_of_perfectField` `Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean:363` | `[Field K][PerfectField K][IsReduced X]` + LocallyOfFinitePresentation | **EXISTS, PerfectField** ✓ |
| `PerfectField` from char 0 | `PerfectField.ofCharZero` `Mathlib/FieldTheory/Perfect.lean:304` (an **instance**) | `[CharZero K]` | **auto-resolves for ℝ** ✓ |

### Route 1 — what's a GENUINE GAP (small)

- **The chart-sweep `δ`-shift over ℝ** (`varietyDim_ℝ(fibre) = varietyDim_ℝ(orbit-of-realizerD) + δ`):
  the fibre is not the bare orbit closure — the dimension passes through
  `ChartSweepWiring.sweep_of_localizedChartAlgEquiv` (`varietyDim Σ^r = δ + varietyDim F`) and the
  route-c assembly `ClosureBridge.codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep_closure`
  (`:160`), both `[IsAlgClosed k][CharZero k]`. The chart `AlgEquiv` (`ChartLocalizedAlgEquiv`, 0 alg-
  closed uses), `SchurSideNoDrop` (0), `DeterminantalBaseElimination` (0) are already field-generic; the
  alg-closed enters via `SourceNoDrop` (1, the source no-drop pp-cert) and `ClosureBridge` (4, the
  orbit-codim = C piece, which traces to the same orbit smooth-point squeeze). Granularity decides
  whether to relax this whole layer (Granularity 1) or bypass it (Granularity 2 — below).

### What is genuinely ABSENT (confirming thread 07 — these are NOT on the route)

- real radical / real Nullstellensatz / `vanishingIdeal` base-change / semialgebraic dim / `ringKrullDim`
  scalar-extension invariance — **all absent, and the squeeze route needs NONE of them.** The only repo
  alg-closed-GENUINE result in the dim story is `vanishingIdeal_isRadical` (`NullstellensatzCodim.lean:69`,
  the strong Nullstellensatz) — and the squeeze does not use it.

### Route 2 (ℚ-unirationality) — inventory

- The orbit IS banked as an image of a ℚ-rational map: `range_orbitMap` (`OrbitVariety.lean:44`), the
  pullback `orbitPullback M` into `groupRing d` (defined over ℚ). BUT: Mathlib v4.29 has **no**
  "unirational/dominant over an infinite field ⟹ rational points Zariski-dense", no real-point-density
  API, no rational-map dominance theory. Route 2 needs all of this from scratch. **Dominated by Route 1.**

---

## Deliverable 2 — ROUTE RECOMMENDATION

**Route 1 (smooth-real-point SQUEEZE via `finrank(range δ⁰)`), with the crux being
`IsAlgClosed → PerfectField` relaxation of the orbit-dimension chain.** Reasoning:

1. **Reuses the entire banked orbit-dimension chain** — `varietyDim(orbit) = finrank(range δ⁰)` is
   already proved; the ONLY new content is weakening `[IsAlgClosed]` to `[PerfectField]` (or
   `[CharZero][Infinite]`) on a chain whose alg-closedness is vestigial (declared in `variable` blocks,
   consumed only to derive `PerfectField`).
2. **It is an ALGEBRAIC squeeze, not the analytic real-IFT.** Both `varietyDim_ℝ` and `varietyDim_K`
   become the SAME field-independent integer-matrix rank `finrank(range δ⁰)`. The smooth-real-point fact
   enters only as the LOCAL equidimensionality `varietyDim_ℝ = ringKrullDim(ℝ[x]/I localized at M)`,
   which is field-generic (`ringKrullDim_localizationAtPrime_isMaximal_eq_fintype`, `[Field k]` only) —
   so the `x²+y²` trap (the real point set being a lower-dim real form) is dissolved by the algebraic
   smoothness of `orbitRing_ℝ M` at the rational point `M`, not by a density theorem.
3. **NB on the brief's framing:** the brief's "Route 1 (IFT)" lists `pderiv ↔ fderiv` + analytic IFT +
   manifold-dim as crux bridges. **None of those are needed.** The repo's smooth-point machinery is the
   ALGEBRAIC IFT (étale-over-affine-space + cotangent = Krull-dim, `SmoothLocalRelativeDimension` +
   `SmoothPointRegular`), all field-generic / PerfectField. The recommended route is the brief's "Route 1"
   *spirit* (smooth rational point ⟹ local dim) executed **algebraically**, which is far cheaper.
4. Codex (decorrelated, xhigh) independently recommended Route 1 with the SAME `IsAlgClosed → PerfectField`
   relaxation and flagged Route 2 as needing absent infra. Full decorrelation.

**Crux rung (the single hardest):** the `IsAlgClosed → PerfectField` relaxation of A6.1
`finrank_range_deformationδ_le_varietyDim` and its transitive deps (M3 cotangent, orbit smooth point,
orbit primeness). Low MATH risk (the in-file docstrings already assert PerfectField suffices), bounded-
but-real Lean risk (sweep the chain; some `variable [IsAlgClosed k]` blocks; check no hidden consumer).

---

## Deliverable 3 — the exact LEMMA LADDER (Route 1)

Two granularities. **Recommend Granularity 2 first** (the abstract-dim squeeze — minimal, lands T′
directly) with **Granularity 1 as the earned extension** (relax the full `=C+δ` chain — gives the real
codim formula as a theorem, retiring `hT` entirely rather than just discharging it).

### Granularity 2 — the MINIMAL ladder to `T′` (recommended build order)

Each rung: **target** | *Mathlib/banked lemma it uses* | **gap to build**.

- **L1. `dense_smoothLocus` over ℝ** — *uses* `Scheme.Hom.dense_smoothLocus_of_perfectField` (EXISTS,
  PerfectField) + `PerfectField.ofCharZero`. **gap:** none — instance resolves. (Sanity rung.)
- **L2. Orbit primeness over `[Infinite k]`** — relax `isPrime_vanishingIdeal_orbitSet` `[IsAlgClosed k]
  → [Infinite k]`. *uses* its own proof (already `[Infinite k]`-only via `vanishingIdeal_range_orbitMap
  _eq_ker`). **gap:** change the hypothesis + chase the `variable` block in `OrbitVariety`.
- **L3. Orbit smooth at the rational point M over `[PerfectField k][Infinite k]`** — relax
  `exists_orbitPointIdeal_isSmoothAt` / `isSmoothAt_normalFormIdeal`. *uses* `dense_smoothLocus_of_
  perfectField` + `dense_orbitSpecSet` (relax to `[Infinite k]`, proof uses generic
  `zeroLocus_vanishingIdeal_eq_closure` + `vanishingIdeal_orbitSpecSet_eq_bot`). **gap:** relax
  `[IsAlgClosed]` to `[PerfectField][Infinite]` across `OrbitSmooth`'s SpecModel section.
- **L4. M3 cotangent = dim over `[PerfectField k]`** — relax `smooth_point_isRegularLocalRing` +
  `finrank_cotangentSpace_eq_of_isSmoothAt` + `finrank_cotangentSpace_le_of_isSmoothAt`
  (`SmoothPointRegular`). *uses* `ringKrullDim_localizationAtPrime_eq_of_isSmoothAt` (already `[Field k]`)
  + the residue-field-formally-smooth-over-perfect step (`FormallySmooth.of_perfectField`). **gap:** the
  in-file docstring (`:21`) already says PerfectField suffices — relax the hypothesis, it should go
  through. **(THE CRUX RUNG — flagged.)**
- **L5. A6.1 reverse over `[PerfectField k][Infinite k]`** — relax `finrank_cotangent_eq_varietyDim` +
  `finrank_range_deformationδ_le_varietyDim` (`OrbitTangentCotangent`). *uses* L2/L3/L4 + GAP3
  `ringKrullDim_localizationAtPrime_isMaximal_eq_fintype` (field-generic) + GAP2 residue-field-`k` bridge
  (rational point, field-generic). **gap:** relax + re-thread the `[IsAlgClosed]` deps now relaxed in
  L2–L4.
- **L6. Orbit-dim EQUALITY over ℝ** — `varietyDim_k(orbitRankLocus M) = finrank_k(range δ⁰_M)`, over
  `[CharZero k][Infinite k]`. *uses* the unconditional `≤` (`OrbitDifferentialRank.lean:664`, holds over
  ℝ) + the relaxed `≥` (L5), `le_antisymm`. **gap:** assemble (new lemma; the `VoigtDischarge` squeeze
  relaxed).
- **L7. `finrank(range δ⁰)` is base-change invariant** — `finrank_ℝ(range δ⁰_M) = finrank_K(range
  δ⁰_(M.map ι))`. *uses:* `deformationδ` is a `k`-linear map with INTEGER (0/1) structure matrix
  (`realizerD` = interval direct sum); rank of an integer matrix is field-independent in char 0.
  **gap:** a `deformationδ` base-change/rank-invariance lemma (entries are the same integers; could route
  via `Matrix.rank` over ℤ cast, cf. `lean/CLAUDE.md` "Matrix-product identities over ℤ then cast").
  *Minor risk:* `deformationδ` is defined as a `LinearMap`, not a `Matrix` — may need a `toMatrix'` bridge
  or a direct `finrank(range) ` base-change argument. **Probe this rung's exact shape early.**
- **L8. The `δ`-shift over ℝ for the FIBRE** — `varietyDim_ℝ(fibre ℝ B) = varietyDim_ℝ(orbit of
  realizerD over ℝ) + δ`. *uses* `ChartSweepWiring.sweep_of_localizedChartAlgEquiv` + the route-c
  assembly, relaxed to `[PerfectField/CharZero/Infinite]`. **gap:** relax `SourceNoDrop` (1 use) +
  `ClosureBridge` (4 uses) — the `ClosureBridge` uses trace back to the orbit-codim = C piece (L6).
  *(This is where Granularity 2 still touches the chart layer; if it gets heavy, fall to the alternative
  below.)*
- **L9. Assemble `T′`** — `varietyDim_ℝ(fibre ℝ B) = varietyDim_K(fibre K B)`: chain L8(ℝ) + L7 +
  L8(K, banked) — both sides `= finrank(range δ⁰) + δ`. *uses* the above. **gap:** the final `T′`
  statement at the `canonicalCoord d '' fibre` shape the reduction consumes; + general-rank real-fibre
  nonemptiness (`fibre_normalForm_nonempty` is `[Infinite k]` — holds over ℝ; deferred side rung for
  arbitrary `B`, present for `B=0`).
- **L10. Discharge `hT`** — feed `T′` + nonemptiness to the banked
  `codimRealFibre_eq_codimRepCanonical_of_dimTransfer` (`RlctPayoff.lean:404`). **gap:** none — banked.

**Alternative for L8 (if the chart relax is heavy):** prove the fibre-dim transfer WITHOUT the chart by
transferring at the determinantal-locus level directly — `varietyDim_ℝ(Σ^r over ℝ) =
finrank(δ⁰ at realizerD) + (sigma δ-piece)` using the sigma-side squeeze (`SigmaCodim`,
`SigmaComponents`), then the fibre = sigma minus the GL-bundle. This avoids the localized chart but needs
the sigma-side dimension squeeze relaxed instead. **Probe which layer is lighter to relax** in Wave 1.

### Granularity 1 — the EARNED extension (relax the full `=C+δ` chain over ℝ)

If L1–L6 land cleanly, the same relaxation propagated through `VoigtDischarge` +
`codimRepCanonical_orbitRankLocus_eq_multSum` + `FibreCodimFinal` yields
`codimRepCanonical (k:=ℝ) (fibre ℝ B) = C + δ` **as a theorem over ℝ** — i.e. the real codim formula,
retiring `hT` outright (not just discharging it). This is the bedrock-completion move (the boundary the
chain already promised, now filled over ℝ). Larger refactor (~55 files mention `IsAlgClosed`, but most
are vestigial); recommend as the second wave once the squeeze core (L1–L7) is proven to relax.

---

## Deliverable 4 — banked DLNFibre assets to build on (names VERIFIED in-tree)

- `realizerD` — `ThetaComponentCount.lean:117` (interval-direct-sum realizer of a Kostant partition;
  0/1 entries, defined over ℚ). `rankPattern_realizerD` `:124`.
- `deformationδ` — `DeformationExt.lean:57` (the orbit tangent `k`-linear map); `finrank(range δ⁰)`
  is the orbit-dim invariant.
- catenary — `RadicalCatenary.codimRepCanonical_add_varietyDim_eq_card_of_nonempty` `:179` (field-generic);
  `height_vanishingIdeal_add_varietyDim_eq_card` `NullstellensatzCodim.lean:147` (bedrock).
- `codimRepCanonical` — `OrbitCodim.lean:133`; `varietyDim` — `NullstellensatzCodim.lean:139`.
- the squeeze halves — `varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional`
  `OrbitDifferentialRank.lean:664` (≤, over ℝ already); `finrank_range_deformationδ_le_varietyDim`
  `OrbitTangentCotangent.lean:641` (≥, relax this).
- A0 link — `varietyDim_eq_ringKrullDim_range_orbitPullback` `OrbitPullbackDim.lean:74` (`[Infinite k]`).
- trdeg core — `JacobianTrdeg.diffIndepCriterion_proof` `:118` + `trdeg_adjoin_le_genericDifferentialRank`
  `:201` (`[CharZero k]`).
- smooth-dim — `SmoothLocalRelativeDimension.ringKrullDim_localizationAtPrime_eq_of_isSmoothAt` `:113`
  (`[Field k]`); `SmoothPointRegular.{smooth_point_isRegularLocalRing:167, finrank_cotangentSpace_eq_of_
  isSmoothAt:198}`.
- chart-sweep — `ChartSweepWiring.sweep_of_localizedChartAlgEquiv` `:107`;
  `ClosureBridge.codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep_closure` `:160`;
  `FibreCodimFinal.{fibre_normalForm_nonempty:42, codimRepCanonical_fibre_eq_cCodim_add_shift:170}`.
- the discharge target — `codimRealFibre_eq_codimRepCanonical_of_dimTransfer` `RlctPayoff.lean:404`.
- `codimRepCanonical_orbitRankLocus_*` brief-named family — in `ThetaComponentCount.lean` / `ClosureBridge`
  (e.g. `codimRepCanonical_orbitAsTuples_realizerD` `ClosureBridge.lean:71`, the orbit-codim=C piece).

## Deliverable 5 — cost / risk

- **#tides:** Granularity 2 (T′ only): **~3–4 tides.** (T1: relax L2–L5 the orbit smooth-point squeeze
  core — one connected sweep, the crux. T2: L6+L7 the orbit-dim equality + δ⁰ base-change rank
  invariance. T3: L8+L9 the δ-shift over ℝ + assemble T′ + discharge hT. A possible T4 if L8's chart
  relax forks to the alternative sigma route.) Granularity 1 (full `=C+δ` over ℝ): **+2–3 tides** of
  mechanical `IsAlgClosed → PerfectField` propagation across the chart/Voigt chain.
- **Biggest unknown:** **L7** — whether `finrank(range deformationδ)` base-change invariance is a clean
  lemma. `deformationδ` is a `LinearMap` (not a `Matrix`); need either a `toMatrix'` integer-matrix
  bridge + field-independent rank, or a direct base-change-of-range-finrank argument. Probe its exact
  shape FIRST (it gates the squeeze-to-equality). Second unknown: **L8** chart relax vs the sigma-side
  alternative — which layer is lighter.
- **Genuinely-hard NEW math:** **NONE.** Every rung is either (a) relax a vestigial `[IsAlgClosed]` to
  `[PerfectField]`/`[Infinite]` on an already-proved lemma (the in-file docstrings assert this suffices),
  or (b) assemble banked pieces (`le_antisymm`, integer-rank invariance, the banked reduction). This is
  the decisive contrast with thread 07's "(a)/(b)/(c) all blocked" — thread 07 was scoping a *generic*
  real-dim transfer; the DLN fibre's orbit-closure structure makes it a SQUEEZE to a field-independent
  rank, sidestepping every absent real-AG primitive.
- **Placement: `DLNFibre.Core`** — confirmed. The relaxed orbit-dimension squeeze is network-free engine
  (it is the existing `Core` orbit machinery with weaker hypotheses); reusable; eventual Mathlib-upstream
  candidate ("reduced finite-type domain over a perfect field: variety dim = orbit-tangent rank, base-
  change invariant"). T′ + the discharge wiring touch `DLN/RlctPayoff` (the consumer), but the math lives
  in `Core`.

## Deliverable 6 — decorrelated Codex

`codex/realag-route-prompt.md` (value-withheld: frame + banked facts in, route-truth-value OUT) +
`codex/realag-route-answer.md`. Codex (gpt-5-codex, high) independently: Q1 rank field-independent (yes,
largest nonvanishing integer minor); Q2 smooth⟹regular is PerfectField-only (Stacks 00T2/01V5, char 0 ⟹
perfect, no alg-closed); Q3 the `x²+y²` trap dissolved by the smooth rational point of full local dim;
Q4 the `×A^δ` factor adds dimension over both fields, no subtlety; **Q5 Route 1 recommended, the
`IsAlgClosed → PerfectField` relaxation sound — the only alg-closed entry points are (a) smooth⟹regular
[valid over perfect] and (b) orbit irreducibility [valid over any field]; no closed-point=k-point /
Nullstellensatz dependence.** Full convergence with my independent read.

## Registers

- **[Observation]** The orbit-dimension chain's `[IsAlgClosed k]` is uniformly vestigial — declared in
  `variable` blocks, consumed only to derive `PerfectField k`; ℝ is `CharZero ⟹ PerfectField`.
- **[Claim]** T′ is bounded-provable at Mathlib v4.29 via the squeeze (Granularity 2, ~3–4 tides), no
  new hard math. **Kill-condition (stated before confirming):** a rung in the L2–L8 chain genuinely
  consumes alg-closedness beyond `PerfectField` (e.g. a closed-point = `k`-point identification, a
  strong-Nullstellensatz `vanishingIdeal = radical` step, or a residue-field-is-`k` use that fails for a
  non-`k`-rational point). **Stress-test result: did NOT fire** — audited `OrbitSmooth` (smooth point via
  `dense_smoothLocus_of_perfectField`), `OrbitVariety` (primeness = `RingHom.ker_isPrime`, `[Infinite]`),
  `SmoothPointRegular`/`OrbitTangentCotangent` (cotangent=dim via residue-field-formally-smooth-over-
  perfect + the `k`-RATIONAL point M, so GAP2 residue=`k` holds at M specifically, not a generic
  closed point), `NullstellensatzCodim` (the squeeze uses the field-generic `height + varietyDim = card`,
  NOT `vanishingIdeal_isRadical`). The one strong-Nullstellensatz result is off the squeeze path.
- **[Speculation]** Granularity 1 (full `codim_ℝ = C` over ℝ) is reachable as the earned bedrock
  extension once the squeeze core relaxes — would retire `hT` as a theorem, not a discharged hypothesis.
- **[Question]** L7: cleanest Lean shape for `finrank(range deformationδ)` base-change invariance given
  `deformationδ` is a `LinearMap` over `k` (not a bare integer `Matrix`)? Probe first.

## Reflection

Most likely to advance: **the L2–L5 orbit smooth-point squeeze relaxation** (the crux) — it unlocks the
whole route and is low-math-risk (docstrings pre-assert PerfectField suffices). Most likely to break:
**L7** (δ⁰ base-change rank invariance — a `LinearMap`-not-`Matrix` packaging snag, not a math one) and
**L8** (the chart relax — could be heavier than the orbit core, hence the sigma-side fallback). Next
computation that clarifies: a one-tide PROBE that (i) relaxes `finrank_range_deformationδ_le_varietyDim`
to `[PerfectField k]` and green-builds it over `ℝ` on a concrete witness, and (ii) pins the exact
`deformationδ` base-change lemma shape — these two settle the crux + the biggest unknown before the full
build commits.
