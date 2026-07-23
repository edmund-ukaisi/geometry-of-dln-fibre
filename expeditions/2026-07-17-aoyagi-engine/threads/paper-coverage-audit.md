# Paper-coverage + functional-fidelity audit — AOYAGI 2023 axis (operator commission, task #63)

**Charge (operator, 2026-07-23):** *"what in the Aoyagi paper have we not constructed, and for those that we
have, do they cover all intended mathematical function?"* — the completeness twin of the #31 fidelity
review. **Scope (operator-pinned):** Aoyagi 2023 alone — every definition, lemma, theorem, and **proof
step** of the paper → its Lean home → classification. (Lehalleur–Rimányi is out of the commissioned scope;
its geometry was known-complete from prior expeditions and is demoted to Appendix A as context.)

**Sources (exact paths).** Paper: `paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/aoyagi-2023-neural-networks-preprint.pdf`
(31 pp.). Reproduction: `theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex`. The chunk-by-chunk PDF-image
walk and its errata live in `theory/aoyagi-2023-reproduction/worked-tex-errata.md`.

**Method.** (1) PDF-image walk of the paper (chunks C0–C13, see the errata doc); per chunk, tag the Lean
render. (2) Lean-side homes from four decorrelated fan-out reads of `lean/DLNFibre` + `ROADMAP.md`, with the
cited-axiom set and the sorry distribution re-derived directly (41 real `sorry` tactics: 25 in `DLN/RLCT/`,
16 in `DLN/Aoyagi/`, **zero in Core geometry**; 3 `@[cited]` axioms). Classifications: **CONSTRUCTED** (full
function / shadow) · **PARTIAL** · **FRONTIER-OWNED** (named sorry) · **NOT CONSTRUCTED** (planned /
UNPLANNED) · **CITED**.

## §0. The finding in one paragraph

Aoyagi's **value chain given a resolution** is fully built, cite-free, at arbitrary `d`: Lemma 1
(ideal-invariance), the monomial rule + the min-over-charts atlas, the `M_{s,k}` pole-order extraction, and
the arithmetic minimisation (Lemma 3, the closed form) all land sorry-free. Her **learning-coefficient value**
`λ = C/2` is a theorem two ways — a cite lane (general rank `r`, resting on the two `@[cited]`
Watanabe+Aoyagi axioms) and a cite-free build lane (`r=0`, reducing to the single frontier
`exists_coreResolution`). What is genuinely **open** is the *construction of the resolution itself* — the
recursion's **invariant maintenance** (the case-1/case-2 `stepInv` leaves, the wall #38, the descent cap) and
the **geometric cover** (L5/L7) — i.e. Aoyagi's Cases-1&2 blow-up made rigorous. Her **order** `θ = a(ℓ−a)+1`
(the pole multiplicity / rlcm) is defined combinatorially (`aoyagiPoleOrder`) but its **analytic binding to
the zeta pole is NOT constructed** (a named deferred seam). **No unplanned gap:** every open item is on the
ROADMAP or a named frontier.

## §1. The Aoyagi-axis coverage matrix (headline)

Rows follow the paper's own order (chunk ids C0–C13 map to the errata doc). Legend: **C**=constructed
sorry-free · **C\***=constructed, scope-narrowed (see §2) · **C(cite)**=constructed modulo a named citation ·
**FR**=frontier-owned (named sorry) · **ND**=not constructed (planned/unplanned) · **CITE**=deliberate cite.

| # | Aoyagi object / step | Source | Lean home | Class | Functional note |
|---|---|---|---|---|---|
| C0 | DLN model + square loss; zero-set = optimal set | pp.2,8 | `DLN/RlctPayoff.lean:112` `lossDLN`; `:127` `zeroLocus_lossDLN_eq_fibre` | C | arbitrary `d`, ℝ |
| C0 | loss-RLCT = Kullback-RLCT (the statistical reading) | p.3 | — | CITE | SLT monument (off value path); O7(b) |
| C1 | Def 1 — rlct value `λ` (and order) | p.5 | `Core/Analysis/RLCT/{Local,Global}.lean` `rlctAt`,`rlctGlobal` | C | cite-free; the pole **order** `m` is define-only (`Pair.lean`), its DLN identification = seam (C12) |
| C1 | **Lemma 1** — RLCT ideal-invariance | p.5 | `Core/Aoyagi/IdealInvariance.lean` (`rlctAt_sumSqFam_le_of_germRepresents` + eq + weighted) | C | full function (`≤`, equality, weighted). **Errata E-1** (worked.tex:166 printed the inequality flipped; Lean was always correct; fixed e02610619) |
| C1 | Def 2 — `‖C‖`, `⟨C⟩` | p.5 | implicit (Frobenius, ideal) | C | trivial |
| C2 | Hironaka monomial rule `λ=min_U min_j (h_j+1)/(2k_j)` | p.6 | `Core/Aoyagi/MonomialRLCT.lean:432` (per-chart); atlas `ProductResolution.lean:540` `rlctAt_sumSqFam_eq_iInf_charts` | C | full function; the once-open "min over charts" (O1) has **LANDED**. Hironaka existence for arbitrary loss = CITE, but unused (the DLN build makes its own charts = C9) |
| C3 | **Thm 1** — RRR (`L=2`) λ value | pp.6–7 | `DLN/RLCT/Validate/…` `case222_rlct` (clean-three); the engine at `L=2` | C | value at `L=2` |
| C3 | Thm 1 order `θ=a(ℓ−a)+1` | p.7 | `DLN/RLCT/Validate/RRR.lean:151` `rrrTheta = aoyagiTheta ℓ a` | C/ND | combinatorial value defined; **analytic binding to the pole = ND** (seam, C12) |
| C4 | **Def 3** — general-`L` M-set | p.8 | `Core/CThetaQIP.lean`,`CThetaValue.lean` (`qipM`,`cValue`); robust `½·Mval_min` | C | Def-3 realised as a computed consequence (the printed cond-(iii) `≤` faithfully carried + flagged (T-D) in worked.tex) |
| C5 | **Thm 2** — general-`L` λ value (3 forms) | p.9 | cite lane `DLN/RlctPayoff.lean:539`,`RlctPayoffGeneral.lean:125`; build lane `DLN/Aoyagi/LearningCoefficient.lean:323` | C(cite) / FR | cite lane: general `r`, rests on the 2 cites (below). build lane: `r=0`, cite-free, reduces to `exists_coreResolution` (FR). Closed form `cValue`/`cCodim` = C, arbitrary `d` via sort |
| C5 | Thm 2 order `θ=a(ℓ−a)+1` | p.9 | `aoyagiPoleOrder ℓ a` (+`ThetaOrderDistinction.lean`) | C/ND | combinatorial value C; **analytic pole-multiplicity binding = ND** (seam) |
| C6 | **Lemma 2** — block elimination `Q₁AQ₂=diag(A₁,C₄)` | pp.10–11 | realised in the monument shears `MonumentAtlas.lean` `canonNormalizationOf` (this expedition's F₂); worked instance `DLN/RLCT/Validate/Case222Lemma2.lean` | FR | the general paired-clearing *maintenance* is inside the monument's open leaves (highest-blast: wall #38) |
| C7 | **Thm 3** — product reduction (peel regular part) | pp.11–13 | `DLN/Aoyagi/LearningCoefficient.lean` `coreReduction`; prefactor `(−r²+r(H¹+H^{L+1}))/2` | C / ND | `r=0` corollary C (sorry-free, via `GlobalHomog`+flatten); **general `r` = ND** (O3, Skeleton lane sorried) |
| C8 | **Thm 4** — reduction to the deepest singular point | p.14 | `r=0` via `GlobalHomog`; general `Skeleton.lean:1140` `rlctAt_deepest_le_of_optimal` | C / FR | `r=0` corner C; general (D1 monotonicity) = FR |
| C9 | recursion: Cases 1(1)/1(2)/2 + rollover/boost-merge | pp.15–22 | `DLN/RLCT/Engine/{ResolutionTree,EngineConstruction}.lean` (`StepCase`,`conOracle`,`buildTree`) | C | the case tree + **total oracle** + reachability: C |
| C9 | termination of the recursion | p.14+ | `EngineConstruction.lean:111,119` `conMeasure`,`conRel_wf` | C | genuine well-founded lex triple |
| C9 | carried invariant `diag(b)·[E_J\|D_J]·∏C` + `b`/`M_{s,k}` ledger — **maintenance** | pp.15–22 | `StepInv`/`foldB`/`foldResid`/`Deg1SupportedSlot`; maintained only at `terminal_edge_stepInv` | FR | the interior leaves are the open frontier: `case1/case2_preserves_stepInv`, `realBranch_boostReady_case11` (**wall #38**), `realBranch_appendResidDescent`, `realBranch_multiAffine_step`, the L2 homogeneity atoms |
| C9 | exhaustion / chart cover | pp.15–22 | combinatorial `OracleInv_conOracle_stepChildren` (C); geometric `leafPath_compactCover` (L7), `leaf_stepInv_of_path` (L5) | C / FR | *combinatorial* exhaustion proved; *geometric* cover (does the fold cover the fibre nbhd) is a named frontier |
| C10 | `M_{s,k}` completion-of-squares → pole order → `C/2` | p.23 | `MonomialRLCT.lean` + `ProductResolution.lean:590` `two_mul_rlctAt_eq_divisorMin` + `Engine.lean:84` | C | **built, sorry-free, cite-free** given a resolution (the value read-off) |
| C11 | **Lemma 3** — within-set balance (the minimisation) | p.24 | `Core/CThetaExplicit.lean` `isLeast_sumSq`; `cValue` | C | the `½(∑q²−∑m²)` closed form; replaces the paper's Conway–Sloane apparatus |
| C12 | **Lemmas 4–5** — the order `θ=a(ℓ−a)+1` | pp.25–27 | `aoyagiPoleOrder`; `DLN/Aoyagi/OrderBinding.lean`, `OrderCount.lean` (combinatorial count) | C / ND | the combinatorial order C; the **analytic pole-multiplicity binding (zeta pole order = `a(ℓ−a)+1`) is ND** — a named deferred seam (`cards/theta-analytic-multiplicity-seam.md`), blocked partly by Mathlib-absent meromorphic continuation |
| — | **Payoff** `rlct(K^DLN)=C/2` ("mildly singular") | p.28/§8 | cite lane (general `r`) / build lane (`r=0`) | C(cite)/FR | as C5; the analytic equality `rlct=½·codim` is the 2 cites |
| — | — Watanabe universal `rlct ≤ ½·codim` | — | `DLN/RLCT/AoyagiCited.lean:57` `cited_watanabe_upper_ax` | CITE | `axiom`, on the payoff path |
| — | — Aoyagi DLN `½·codim ≤ rlct` (singular-locus lower bound) | — | `AoyagiCited.lean:67` `cited_aoyagi_lower_ax` | CITE | `axiom`; the whole lower bound is inside it |

## §2. Functional-fidelity notes (Aoyagi axis)

1. **The two θ's are different objects — and our artifacts keep them apart (reassessed 2026-07-23,
   operator-corrected).** On the **Aoyagi axis**, "θ" is the **order** = the real-log-canonical multiplicity
   (rlcm) = the order of the largest zeta pole = `a(ℓ−a)+1` (`aoyagiPoleOrder`). This is a *different object*
   from the geometric **component count** (L&R's θ = `cTheta`/`numTop`, Appendix A). They coincide only when
   `min(a,ℓ−a) ≤ 1` and diverge otherwise (witness `d=(2,2,2,2,2)`, `r=0`: component count `6` ≠ pole order
   `5`). Our Lean artifacts are **clean** on this: `ThetaOrderDistinction.lean` names `aoyagiPoleOrder` for
   what it is (pole order, explicitly *not* a component count), proves the non-equality
   (`numTop_d22222_ne_aoyagiPoleOrder`), and the analytic θ-binding was *excised* rather than sorry-carried
   (the "mint guard"). A NAME=CONTENT sweep found **no** Lean name or docstring describing `numTop`/`cTheta`
   as a "multiplicity" or `aoyagiPoleOrder` as a "count". *[An earlier draft of this audit (§2.3) claimed an
   "L&R printed rlcm off-by-one erratum"; that conflated the component count with the rlcm and is
   **WITHDRAWN** per the operator — there is no off-by-one; the two are simply different objects. See §5.]*

2. **Aoyagi's order `θ` — combinatorially defined, analytically unbound (the one genuine ND on the value
   side).** `aoyagiPoleOrder ℓ a = a(ℓ−a)+1` exists; binding it to the *actual* pole multiplicity of the DLN
   zeta at `−λ` is the deferred analytic seam (Lemma 5's content). The `λ` *value* headline does not need it.

3. **Field generality (visible, planned).** The `λ` value rides `cCodim` (the codimension), whose theorems
   carry `[CharZero][Infinite]` (+`[IsAlgClosed]` for the component-count side). Over the DLN field (ℝ/ℂ)
   this is the full function; broader field generality is roadmapped (Gap 2), orthogonal to Aoyagi's ℝ result.

4. **φ-form vs φ-free RLCT (O7a, cheap, annotated-not-built).** Aoyagi's Def-1 threshold uses a prior `φ`;
   the Lean `rlctGlobal` is the φ-free Lebesgue threshold. Their equality (φ-independence when `φ(w*)≠0`) is
   buildable-cheap but currently only annotated — the *reading* of `rlctGlobal` as the learning coefficient.

5. **Payoff rank asymmetry across lanes.** The cite lane covers general rank `r` (value
   `(C+r(d₀+d_N−r))/2`); the cite-free build lane is `r=0`. The general-`r` cite-free build is O3 (Thm 3
   gauge-slice + general Thm 4), deferred.

## §3. Ranked gap list (Aoyagi axis)

**Tier 0 — UNPLANNED (dangerous): NONE FOUND.** Every open item is roadmapped or a named frontier. The four
named traps: geometric exhaustion → named frontier (Tier 1 #1); termination → proved; pole-order→C/2 chain →
built cite-free; the order/θ side → defined, with the analytic binding an explicit deferred seam. Boundary
widths (`d_i=1`, non-square) covered (`hpos`; witnesses `(1,2,1)`,`(2,3,2)`).

**Tier 1 — frontier-owned, load-bearing or mis-scoped.**
1. **Geometric exhaustion of the fibre is a frontier, not a theorem** — `leafPath_compactCover` (L7,
   `MonumentAtlas.lean:1821`) + surjectivity via the sorried L5 (`:1763`). The case tree is rendered, total,
   terminating; *that its charts cover a neighbourhood of the fibre* is open. The exact "does the fold
   exhaust the fibre" trap — correctly frontier-owned, ranked here for visibility.
2. **A sorry under a statement flagged REFUTED-AS-STATED** — `DLN/RLCT/Engine/GeoAlphaGauge.lean:675`
   `leafDiagFrob_geoAtlasNorm` (refuted `:666`; no det-1 chart works, honest route is ideal-level). **On the
   board as #66** (retire/restate).
3. **Two superseded "baked" sorries** — `MonumentAtlas.lean:1475/1515` `case{2,1}_preserves_stepInv`,
   superseded by the primed twins. **Folds into the Gap-B fossil disposition #65.**
4. **The monument's live wall (in progress, correctly scoped)** — `realBranch_boostReady_case11`
   (`Case1Wire.lean:395`, task #38), `realBranch_appendResidDescent` (`:1446`),
   `realBranch_multiAffine_step` (`:1362`), the L2 homogeneity atoms. The active frontier (this expedition).
5. **The parallel RLCT-engine analytic sorries** (`DLN/RLCT/`, 25) — heads `sjJointResolution`,
   `deepest_regular_core_normal_form`, `resolution_charts`, the interior-LDU CoV cluster. A **second,
   largely independent** cite-free lane to the same value; consolidating on one would shrink the open surface.

**Tier 2 — NOT CONSTRUCTED, planned-but-distant.**
1. Cite-free `rlct=C/2` (retiring both `@[cited]` axioms) — the monument + RLCT engine; the RLCT-runway
   destination.
2. **The order-θ analytic pole-multiplicity seam** — bind the zeta pole order at `−λ` to `a(ℓ−a)+1`
   (Aoyagi's Lemma 5); blocked partly by Mathlib-absent meromorphic continuation.
3. General-rank `r>0` cite-free build (O3) — Thm 3 gauge-slice + general Thm 4; the single largest add.
4. φ-form fidelity (O7a) — cheap, annotated-not-built.

**Tier 3 — CITED (faithful monuments).** `cited_watanabe_upper_ax`, `cited_aoyagi_lower_ax` (the
`rlct=½·codim` equality, on the payoff path); `cited_local_zeta_pole` (Atiyah/Saito continuation, off the
value path); the loss-RLCT = Kullback-RLCT statistical reading (O7b).

## §4. Answer to the commission, plainly

**What have we not constructed (Aoyagi axis)?** (a) The *resolution itself* — the invariant-maintenance
leaves of her Cases-1&2 recursion + the geometric cover (Tier 1 #1,#4; the wall #38); (b) the *analytic
binding of the order* `θ=a(ℓ−a)+1` to the zeta pole (Tier 2 #2); (c) the general-rank cite-free build (Tier 2
#3). The `λ` *value* `= C/2` is a theorem (cite lane, all `r`; build lane, `r=0`).

**Do the constructed pieces cover the whole function?** The value chain given a resolution (Lemma 1, monomial
rule + atlas, `M_{s,k}` extraction, Lemma 3 minimisation) — **yes**, cite-free, arbitrary `d`. The payoff —
**yes as Aoyagi/L&R state it** (analytic equality honestly cited). The order side — the *value* is defined;
the *analytic function* it plays (pole multiplicity) is the one unbuilt piece on that side.

**No unplanned gap.** The item most resembling the named trap ("does the fold exhaust the fibre") is a named
frontier (L5/L7), owned and in scope.

## §5. Reassessment delta (2026-07-23, operator-directed)

- **§2.3 "L&R printed rlcm off-by-one" — WITHDRAWN.** It conflated the component count (L&R's θ) with the
  rlcm (pole multiplicity, Aoyagi's `a(ℓ−a)+1`); those are different objects, so there is no off-by-one and
  no authors' erratum. §2.1 (the two-objects distinction) is the corrected statement; it survives and matches
  `ThetaOrderDistinction.lean`.
- **NAME=CONTENT sweep — Lean artifacts CLEAN** (one line, per the operator): no Lean name/docstring
  conflates θ-as-count with θ-as-multiplicity; `ThetaOrderDistinction.lean` is the guard.
- **Two prose sites still carry the withdrawn framing (flag for the precision board, not re-adjudicated —
  L&R is out of scope):** `ROADMAP.md` (~L144–149, "off-by-one in LR's printed rlcm") and
  `docs/expositions/theta-invariants-distinction.md` (~L30–31, "L&R's printed rlcm formula … off by one").
  Both should be reconciled with the operator's ruling (banked in `lessons.md` @ 829bea06e).
- **Homes addendum (canonical moved, L3T3 merged 8c2b5253e):** the descent slot + the primed
  `case{1,2}_preserves_stepInv'` twins are now on canonical; the C9 FRONTIER rows above name the current homes.

---

## Appendix A — Lehalleur–Rimányi geometry (context, OUTSIDE the commissioned scope)

*The operator pinned the commission to Aoyagi 2023. The L&R fibre-geometry sweep below is retained as context
— it was known-complete from prior expeditions (all sorry-free, axiom-clean, arbitrary `d`) and is not part
of the Aoyagi-axis deliverable. Kept so the audit is self-contained on where the geometric `C` and the
component-count θ that Aoyagi's `λ=C/2` consumes actually live.*

| L&R item | Lean home | Class | Note |
|---|---|---|---|
| `Rep_d`, `mult`, rank loci, fibre | `Core/Setup.lean:33,51,56,64` | C | arbitrary `d` |
| Fibre codim `= C + r(d₀+d_N−r)` | `Core/FibreCodimFinal.lean:171` | C\* | arbitrary `d`, zero-cite; `[IsAlgClosed][CharZero]`, `Type 0` |
| Gabriel (Thm 2.5) | `Core/Gabriel.lean:275` | C | from scratch |
| Orbits↔Kostant↔rank patterns (Cor 2.9) | `Core/OrbitKostant.lean:104` | C | full bijection |
| Orbit-closure order (Thm 3.8) | `Core/OrbitClosure.lean:993` | C | set + ideal equality |
| `Ext¹` codim (Cor 3.5, Voigt) | `Core/DeformationExt.lean`; `VoigtDischarge.lean:130` | C | unconditional |
| `C=cCodim`, θ=`numTop` (component count) + geom tie | `Core/CTheta.lean:160,166`; `SigmaCodim`, `CCodimZeroStrict` | C\* | the geometric `C` Aoyagi's `λ=C/2` consumes; `θ` here = L&R's component count (≠ Aoyagi's order θ, §2.1) |
| Poincaré (5.5) / QIP (6.1) / explicit (7.10) / perm-inv (5.10) | `Core/QSeriesThm55`, `CThetaQIP(Converse)`, `CThetaValue`, `CThetaPermInvariance` | C | all three forms mutually equal; arbitrary `d` |
