# Paper-coverage + functional-fidelity audit (operator commission, task #63)

**Charge (operator, 2026-07-23):** *"what in [the] Aoyagi paper have we not constructed, and for those
that we have, do they cover all intended mathematical function?"* — the completeness twin of the #31
fidelity review. #31 asked *is what we built faithful?*; this asks *did we build everything, and does each
built piece do the WHOLE job it does in the proof?*

**Auditor:** elder-standing. **Method.** (1) paper-side inventory from the two source papers —
Lehalleur–Rimányi 2024 (the fibre geometry + type-A translation + `(C,θ)` + the `rlct = C/2` payoff, §§2–8)
and Aoyagi (the resolution-of-singularities RLCT computation reproduced in
`theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex`), cross-read against `ROADMAP.md` (the planned
ladder) and the prior owed-math audit (`verify-owed-math-audit.md`); (2) Lean-side inventory by four
decorrelated fan-out reads of `lean/DLNFibre` (851 files); (3) ground-truth recheck of the two load-bearing
facts — the cited-axiom set and the sorry distribution — re-derived directly, not taken from the reports.
Classifications: **CONSTRUCTED** (full function / shadow) · **PARTIAL** · **FRONTIER-OWNED** (named sorry) ·
**NOT CONSTRUCTED** (planned / unplanned) · **CITED** (deliberate monument).

## The finding in one paragraph

The paper's **geometry** — the ambient objects (`Rep_d`, `mult`, the rank loci, the fibres), the type-A
quiver translation (Gabriel, orbits ↔ Kostant partitions ↔ rank patterns, the orbit-closure order, the
`Ext` codimension), and the invariants `(C, θ)` in all three forms (Poincaré series, quadratic integer
program, explicit formula) plus permutation invariance — is **fully CONSTRUCTED, sorry-free and axiom-clean,
at arbitrary dimension vector `d`**. The **payoff** `rlct(K^DLN_B) = C/2` is CONSTRUCTED as a theorem whose
geometric half (`codim = C`) is zero-cite and whose analytic half (`rlct = ½·codim`) rests on **two cited
axioms** (Watanabe's universal upper bound + Aoyagi's DLN lower bound) — exactly the structure of L&R's own
§8, so faithful to the paper. Everything genuinely open is the **from-scratch replacement of that cited
analytic equality**: the Aoyagi resolution monument (`DLN/Aoyagi/`, 16 sorries) and the parallel RLCT
box-finiteness engine (`DLN/RLCT/`, 25 sorries) — 41 sorries total, **all confined to those two build
lanes; the Core geometry has none.** **No unplanned gap was found** — every open item is on the ROADMAP or a
named frontier. The functional caveats worth the operator's eye are narrow and listed in §2/§3.

---

## §1. Coverage matrix

Legend: **C** = constructed sorry-free · **C\*** = constructed, function-narrowed (see note) · **FR** =
frontier-owned (named sorry) · **CITE** = deliberate citation · **ND** = not constructed.

### A. Ambient objects — L&R §4 (network-free `Core`)

| Paper item | Lean home | Class | Generality / functional note |
|---|---|---|---|
| `Rep_d`, composable tuples | `Core/Setup.lean:33` `Tuple`, `multPrefix` | C | arbitrary `d`, any `CommRing` |
| Multiplication map `mult` | `Core/Setup.lean:51` `mult` | C | arbitrary `d`; DLN reuses `Core.mult` |
| Zero-product & rank-`r` loci `Σ^r`, `Σ^{≤r}` | `Core/Setup.lean:56,60`; closed: `RankLocusClosed.lean:153` | C | arbitrary `d, r`; Zariski-closed |
| Fibre `mult⁻¹(B)` | `Core/Setup.lean:64` `fibre` | C | arbitrary `d, B` |
| Fibre **codimension** = `C + r(d₀+d_N−r)` | `Core/FibreCodimFinal.lean:171` `codimRepCanonical_fibre_eq_cCodim_add_shift` | C\* | any rank-`r` `B`, arbitrary `d`, zero-cite. Narrowing: `[IsAlgClosed][CharZero]`, `k : Type 0` (Gap 2) |
| Fibre **θ-count** | `Core/FibreThetaCountUnconditional.lean:118,161` | C\* | arbitrary `d`; `[IsAlgClosed][CharZero]`, `Type 0` |
| Fibre **generic smoothness** | `Core/FibreComponentOrbitTransport…isSmoothAt_sweepFibre_topComponent` | C | unconditional (fp-domain shortcut) |
| Fibre **bundle / local triviality** | `Core/FibreBundleLocallyTrivialFull` (per-pivot Schur atlas) | PARTIAL | honestly **not** bare `locallyTrivial`; residuals roadmapped (fibration-geometry) — see §3 |

### B. Type-A quiver translation — L&R §§2–3 (`Core`)

| Paper item | Lean home | Class | Note |
|---|---|---|---|
| Gabriel decomposition (Thm 2.5) | `Core/Gabriel.lean:275` `exists_barcode_rankPattern` (+uniqueness `:351`) | C | arbitrary `d`, `Field k`; built from scratch (Mathlib-absent) |
| Orbits ↔ Kostant ↔ rank patterns (Cor 2.9) | `Core/OrbitKostant.lean:104` `orbitKostantEquiv`; complete invariant `:70` | C | arbitrary `d`; full bijection |
| Orbit-closure order (Thm 3.8, Abeasis–Del Fra) | `Core/OrbitClosure.lean:993` `image_orbitRankLocus_eq_repClosure_orbitSet` | C | arbitrary `d`; set + ideal equality |
| `Ext¹(M,M)` codimension (Cor 3.5, Voigt) | `Core/DeformationExt.lean:81`; `OrbitLinearCodim.lean:50`; discharged `VoigtDischarge.lean:130` | C | arbitrary `d`; Voigt discharged → unconditional geometric codim |

### C. The invariants `(C, θ)` in three forms + invariance — L&R §§5–7 (`Core`)

| Paper item | Lean home | Class | Note |
|---|---|---|---|
| `C = cCodim`, `θ = numTop` (defs + geometric tie) | `Core/CTheta.lean:160,166`; geom: `CThetaGeometric.lean:72`, `SigmaCodim.lean:136`, `CCodimZeroStrict.lean:889` | C\* | tied to genuine codim/component-count; `[CharZero][Infinite]` (+`[IsAlgClosed]` for θ) |
| Form 1 — Poincaré/Q-series (Thm 5.5) | `Core/QSeriesThm55.lean:104` `thm55`; extraction `QSeriesExtraction.lean` | C | arbitrary `d` |
| Form 2 — QIP + converse (Thm 6.1) | `Core/CThetaQIP.lean`, `CThetaQIPConverse.lean:833` `cCodim_eq_qipMin` | C\* | core proved for `Monotone d`; lifted to arbitrary `d` via sort |
| Form 3 — explicit closed formula (Thm 7.10) | `Core/CThetaValue.lean:583,903`; arbitrary `d`: `CThetaArbitrary.lean:43…` | C\* | as above; `θ = C(m,\|δ\|)` |
| The three forms **mutually equal** | chain via `cCodim`/`numTop` hub (see report) | C | Form-2/3 equalities `Monotone`-gated then lifted |
| Permutation invariance (Cor 5.10) | `Core/CThetaPermInvariance.lean:81,89`; geom `CThetaGeometricPerm.lean:60,73` | C | arbitrary `σ`, `d`, `r` |

### D. The Aoyagi RLCT payoff — L&R §8 + Aoyagi's resolution (`DLN`)

| Paper item | Lean home | Class | Note |
|---|---|---|---|
| Square-Frobenius loss `K^DLN_B` | `DLN/RlctPayoff.lean:112` `lossDLN`; `zeroLocus…eq_fibre :127` | C | arbitrary `d`; zero-set = fibre |
| Generic RLCT foundation (`rlctGlobal`, Def 8.1) | `Core/Analysis/RLCT/{Global,Local,SumSq,…}` | C | cite-free; opaque `rlctReal` retired |
| **Payoff `rlct = C/2`** (cite lane), general `r` | `DLN/RlctPayoff.lean:539`, `RlctPayoffGeneral.lean:125`; discharged `AoyagiCited.lean:97` | C\* | arbitrary `d`, general `r`; **rests on the two cited axioms below** |
| — Watanabe universal `rlct ≤ ½·codim` | `DLN/RLCT/AoyagiCited.lean:57` `cited_watanabe_upper_ax` | CITE | `axiom`, on payoff path |
| — Aoyagi DLN `½·codim ≤ rlct` (the singular-locus lower bound) | `DLN/RLCT/AoyagiCited.lean:67` `cited_aoyagi_lower_ax` | CITE | `axiom`; the whole lower bound lives inside it |
| **Payoff `rlct = C/2`** (build lane, cite-free), `r=0` | `DLN/Aoyagi/LearningCoefficient.lean:323` `aoyagi_learning_coefficient_via_engine` | FR | arbitrary `d` (`Monotone`), `r=0`; reduces to one leaf `exists_coreResolution` (`:311`, sorry) |
| Lemma 1 (RLCT ideal-invariance) | `Core/Aoyagi/IdealInvariance.lean` (Object A) | C | sorry-free |
| Lemma 2 (paired block clearing) | inside monument shears `MonumentAtlas.lean` `canonNormalizationOf` | C | the F₂ property-home render (this expedition) |
| Case tree 1(1)/1(2)/2 + rollover/merge | `DLN/RLCT/Engine/{ResolutionTree,EngineConstruction}.lean` | C | total oracle `conOracle`, `buildTree` |
| **Termination** (decreasing measure) | `EngineConstruction.lean:111,119` `conMeasure`, `conRel_wf` | C | genuine well-founded lex triple |
| **Exhaustion — combinatorial** (every branch is a case) | `EngineConstruction.lean:2185` `OracleInv_conOracle_stepChildren` | C | total-oracle definitional exhaustion |
| **Exhaustion — geometric** (charts cover the fibre nbhd) | `MonumentAtlas.lean:1821` `leafPath_compactCover` (L7); surjectivity via L5 `:1763` | FR | **the "does the fold exhaust the fibre" gap — a named frontier, not proved** (see §3) |
| Carried invariant `diag(b)·[E_J\|D_J]·∏C` maintenance | `MonumentAtlas.lean` `StepInv`/`foldResid`/`Deg1SupportedSlot`; maintained: `terminal_edge_stepInv :1582` only | FR | interior maintenance = the monument's live sorries (§3) |
| Monomialization → pole order → `C/2` (given a resolution) | `Core/Aoyagi/MonomialRLCT.lean:432`, `ProductResolution.lean:590`, `Engine.lean:84` | C | **built, sorry-free, cite-free**; value = min over charts |
| Aoyagi pole-order θ = `a(ℓ−a)+1` (Lemmas 4–5) | combinatorial `boxedOrder`/`aoyagiPoleOrder` built; analytic binding | ND | deferred seam — **distinct from geometric `numTop`** (§2) |
| Zeta / free-energy interpretation (loss-RLCT = Kullback-RLCT) | — | CITE | the SLT monument (`Core/Analysis/RLCT/Cited.lean:117`), off value path |

---

## §2. Functional-fidelity notes (CONSTRUCTED, but read the fine print)

These are built pieces where the *function* deserves a caveat co-located with the claim.

1. **`(C, θ)` field generality (Gap 2, visible, planned).** L&R prove `(C, θ)` over an *arbitrary* field
   (`thm:base_field` §3.4: split orbits, geometric irreducibility). Our theorems carry `[CharZero][Infinite]`
   (codim) and additionally `[IsAlgClosed]` + `k : Type 0` (counts). Over the DLN application field (ℝ/ℂ)
   this is the full function; L&R's field-independence is an *unrealized* generality, not a truth
   restriction. Each hypothesis is a proof-route artifact (ROADMAP Gap 2). **Faithful, scope-narrowed,
   visible.**

2. **Two distinct θ-invariants — do not conflate (machine-verified non-identity).** The geometric
   `θ = numTop = C(m,|δ|)` (top-dimensional components of `Σ̄^r`) is **not** Aoyagi's RLCT pole-order
   `r_order = a(ℓ−a)+1`. They agree iff `|δ| ≤ 1`; witness `d=(2,2,2,2,2)`, `r=0`: `numTop = 6` vs
   `a(ℓ−a)+1 = 5`. The geometric side is built; the analytic pole-multiplicity binding is a **deferred seam**
   (Bundle 4; the opaque placeholder `aoyagiTheta_eq` was *excised*, not sorry-carried — honest). The
   `rlct = C/2` *value* does not need it.

3. **L&R printed rlcm off-by-one (a paper erratum, not ours).** L&R's printed real-log-canonical
   *multiplicity* is `a(ℓ−a)` = `θ − 1` vs their own definition; the correct value is Aoyagi's `a(ℓ−a)+1`.
   Documented (`docs/expositions/theta-invariants-distinction.md`). **The operator may wish to raise an
   erratum/correspondence with the authors.**

4. **φ-form vs φ-free RLCT (O7a, cheap, annotated-not-built).** The paper's Def-1 threshold uses a prior
   `φ`; the Lean `rlctGlobal` is the `φ`-free Lebesgue-local threshold. Their equality (φ-independence when
   `φ(w*) ≠ 0`) is standard and buildable-cheap (a bump-function two-sided bound) but currently only
   annotated. This is the *reading* of `rlctGlobal` as Watanabe's learning coefficient, not the theorem's
   own truth. **Cheap functional-fidelity item.**

5. **Payoff rank coverage is asymmetric across the two lanes.** The **cite lane** covers general rank `r`
   (value `(C + r(d₀+d_N−r))/2`); the **build lane** (cite-free) is `r=0` only. The destination
   (`mult⁻¹(B)`, general `B`) is met by the cite lane. If the goal is the *cite-free* payoff at general `r`,
   that is O3 (deferred, the largest additional build — Thm 3 gauge-slice + general Thm 4).

---

## §3. Ranked gap list

Ranked by the commission's severity order: **unplanned > frontier-mis-scoped > planned-but-distant.**

### Tier 0 — UNPLANNED gaps (the dangerous class)

**NONE FOUND.** Every open item below is on the ROADMAP or is a named frontier with an owning sorry. I
specifically hunted the commission's four example traps: (a) *a fold that renders the case tree but never
proves it exhausts the fibre* → the combinatorial exhaustion is proved, the geometric cover is a **named
frontier** (Tier 1 #1), not silent; (b) *a termination measure never formalized* → `conMeasure`/`conRel_wf`
is a genuine well-founded relation, **proved**; (c) *pole-order extraction living in the cite when part is
buildable* → the monomialization → pole-order → `C/2` chain is **fully built, cite-free** (given a
resolution); (d) *the θ/count side silently absent* → built (`numTop`), with the analytic-multiplicity
boundary explicitly stated (§2.2). Boundary widths (`d_i = 1`, non-square) are covered (`hpos : 0 < d k`;
witnesses on `d=(1,2,1)`, `(2,3,2)`).

### Tier 1 — frontier-owned, load-bearing or mis-scoped (attention warranted)

1. **Geometric exhaustion of the fibre is a frontier, not a theorem** (`MonumentAtlas.lean:1821`
   `leafPath_compactCover` L7; chart↔leaf surjectivity via the sorried L5 `leaf_stepInv_of_path :1763`).
   This is the single most important functional caveat on the cite-free build lane: the case tree is
   rendered, total, and terminating, but *that its charts cover a neighbourhood of the fibre* is open. Every
   downstream "the resolution exists" claim (`exists_coreResolution`) inherits it. **Correctly frontier-owned;
   flagged here because it is the exact trap the commission named.**

2. **A frontier sorry sitting under a statement known-refuted-as-stated** (`DLN/RLCT/Engine/GeoAlphaGauge.lean:675`
   `leafDiagFrob_geoAtlasNorm`, flagged refuted `:666`). No det-1 chart change-of-variables gives a diagonal
   bounded-below residual; the honest route is ideal-level. This sorry is documented, not silent, but it is
   **mis-scoped** — a `sorry` that reads as fillable under a statement that cannot be filled as written should
   be *retired or restated*, not left in place. **Recommend: restate to the ideal-level obligation or delete.**

3. **Two superseded "baked" sorries kept alongside their live twins** (`MonumentAtlas.lean:1475`
   `case2_preserves_stepInv`, `:1515` `case1_preserves_stepInv`) — superseded by the primed
   `case{1,2}_preserves_stepInv'` in `Case{1,2}Wire.lean`. Dead sorries carried as history. **Hygiene: prune
   or clearly mark as historical-only, so the live count is not inflated.**

4. **The monument's live wall (in progress, correctly scoped).** `realBranch_boostReady_case11`
   (`Case1Wire.lean:395`, task #38), `realBranch_appendResidDescent` (`MonumentAtlas.lean:1446`, the coupled
   corank-≥2 confinement), `realBranch_multiAffine_step` (`:1362`), and the L2 homogeneity atoms
   (`coreGen_layerHomogeneous :1392`, `foldResid_layerHomogeneous :1416`, tasks #6/#8). These are the active,
   properly-scoped frontier — the F₂ property-home render (this expedition) is the current work on them.

5. **The parallel RLCT-engine analytic sorries** (`DLN/RLCT/`, 25). Load-bearing heads: `sjJointResolution`
   (`RouteMSJResolution.lean:803`), `deepest_regular_core_normal_form` (`Skeleton.lean:1094`),
   `resolution_charts` (`Skeleton.lean:1197`), the interior-LDU CoV cluster
   (`RouteMInteriorLDUContract.lean`, 9). This is a **second, largely independent** build of the same value
   via box-finiteness; its sprawl (hundreds of `Route*`/`Deepest*` files) is the largest single body of open
   work. **Note for the operator: two cite-free lanes to the same `rlct=C/2` are in flight; consolidating on
   one would reduce the open surface.**

### Tier 2 — NOT CONSTRUCTED, planned-but-distant (on the ROADMAP)

1. **The cite-free `rlct = C/2`** (retiring `cited_aoyagi_lower_ax` + `cited_watanabe_upper_ax`) — the entire
   monument + RLCT-engine build. This is the RLCT-runway destination; distant by design.
2. **θ analytic pole-multiplicity seam** — bind the DLN zeta's pole order at `−λ` to `a(ℓ−a)+1` (never to
   `numTop`). Blocked partly by Mathlib-absent meromorphic continuation. Deferred (Bundle 4).
3. **General-rank `r>0` cite-free build** (O3) — Thm 3 gauge-slice normal form + general Thm 4; the single
   largest additional build; shares no dependency with the `r=0` kill-path.
4. **Field generality Gap 2** — counts over non-closed / char-`p` / finite fields. Planned, low priority
   (orthogonal to the ℝ/ℂ payoff).
5. **Fibre bundle → bare scheme-theoretic `locallyTrivial`** — projection compatibility + overlap cocycle
   (`targetOverlapTransition`) + the S2b conormal companion; the fibration-geometry residuals. Roadmapped.
6. **Explicit-formula syntactic shape** (Gap 3) — `cValue` proved `= codim` but not rendered in L&R's exact
   fractional-part form; semantically equivalent. Minor.

### Tier 3 — CITED (deliberate monuments, faithful)

- `cited_watanabe_upper_ax`, `cited_aoyagi_lower_ax` (`AoyagiCited.lean:57,67`) — the `rlct = ½·codim`
  equality, on the payoff path. Faithful to L&R §8 (they cite Aoyagi).
- `cited_local_zeta_pole` (`Core/Analysis/RLCT/Cited.lean:117`) — Atiyah/Saito meromorphic continuation;
  off the value path (enriches `(λ, m)` only).
- The statistical layer (loss-RLCT = Kullback-RLCT, O7b) — the SLT monument, cited by design.

---

## §4. Answer to the commission, plainly

**What have we not constructed?** Only the *from-scratch replacement of the cited analytic equality*
`rlct = ½·codim` (the monument + RLCT engine, ~41 sorries in two lanes) and a short list of roadmapped
extensions (Tier 2). Nothing in the paper's **geometry** is unbuilt.

**Do the constructed pieces cover the whole function?** The geometry engine: **yes**, at arbitrary `d`,
sorry-free — with one visible, planned scope narrowing (field generality, §2.1). The payoff `rlct = C/2`:
**yes, as L&R state it** — the geometric half zero-cite, the analytic half honestly cited (§1.D, Tier 3).
The functional watch-items are the five in §2, chiefly the two-θ distinction (§2.2) and the L&R printed-rlcm
off-by-one (§2.3, an authors' erratum).

**No unplanned gap** (§3 Tier 0). The one item that most resembles the commission's named trap — *does the
fold prove it exhausts the fibre* — is a **named frontier** (`leafPath_compactCover`, §3 Tier 1 #1), owned
and in scope, not silent.
