# Retro facet — machinery inventory & the "rising sea" predictability question

**Expedition:** `aoyagi-full` (`origin/expedition/aoyagi-full`, forked at `413566b3`, a 2026-06-25 merge
of `expedition/fibre-codim`; branch tip `a30408dbb`, 2026-07-15 09:47). 3012 commits since fork.
**Author seat:** research-process archaeologist. **Method:** git first-add dates (`--diff-filter=A`
across all reachable branches, since analytic Lean lands on tide branches not the ledger tip), the
June reproduction (`theory/aoyagi-2023-reproduction/`), and the controller ledgers
(`endgame-lanes.md`, `synthesis.md`).

> **Load-bearing scope caveat (read first).** At the fork point the expedition is **not closed**. The
> mint `aoyagi_learning_coefficient_gen` is still gated on a `sorry`: `RouteMSJDeeperFlagCore.lean` has
> 12 `sorry`, and `headSplit_domination` + `hDescent` are open at the capstone base `f483692ef`. The
> **final route was fixed by adjudication, not by a green build** — `routeverify` (2026-07-15 LATE-5,
> `endgame-lanes.md:62`) delivered the VERIFIED spec = the **coupled incidence-direct route**, the
> capstone tide was *spawned* (07-15 09:27) but had not landed. So "the machinery that ultimately
> carried the proof" means, precisely, *the machinery the verified final spec calls for* — the
> banked-and-fidelity-passed incidence charts + the domain-general matrix-integral atoms they consume.
> This distinction matters for every "survived" call below.

---

## 1. Inventory

Dates = first landing of the module *anywhere on the reachable branch set* (analytic Lean lands on tide
worktrees). "First mention" = earliest naming of the move in reproduction / ledger.

| Family (module / lemma) | First mention | Landed | Trigger (which wall) | Predictable from reproduction? | Route-survival |
|---|---|---|---|---|---|
| **Radial/polar CoV** — `S1RadialMorse`; `RouteMSJRadialPolar`; `pivotBlock_radial_blowup` (`RouteMSJPivotBlowup`) | repro (blow-up, §blowup) | 2026-06-25 (Morse atom); 07-10 (RadialPolar); 07-13 (PivotBlowup) | resolving `‖·‖²`-monomial after blow-up | **Yes** — repro §blowup names "recursive blow-up", radial `C³` blow-up | **Survived** — reused in cover, route-B, deep-floor, incidence |
| **Det-Gram / Wishart corank integrability** — `detGram_lintegral_box_lt_top`, `shell_corankOffSector_le_unif`, `shellCorankWeight_le_unif` | endgame (couplingfin) | ~07-11→07-13 | corank-Gram divisor `∫det(Q_bQ_bᵀ)^{−a/2}` finiteness | **Partly** — repro implies the corank/codim charge; the *box-integrability threshold* (`a<m−b+1`) is emergent | **Survived** — consumed by the incidence cert (corank-Gram Wishart threshold) |
| **Singular-value / Ky-Fan dim-counting** — `RouteMSJKyFan`, `shell_subset_goodSet` | endgame (t2adjud §4) | 2026-07-13 | the deep-factor *floor* `Z_deepZ_deepᵀ⪰ε'²U_sU_sᵀ` for the off-shell full-block route | No — emergent from the deep-floor route architecture | **Banked-but-superseded** — the floor is the off-shell route `thresholdhunt` killed; the atom is general but its *consumer* died |
| **Spectral / eigenframe (Brick F)** — `RouteMSJMeasurableEigendecomp` (2 `sorry`), `…Eigenframe`, `…OrderedRootsMeasurable`, `exists_headSplitFrame` | endgame | 2026-07-13 | global measurable diagonalisation for the frame | No — Lean-architecture-emergent | **Banked-but-superseded** — `wallfin`: global route = "genuine Mathlib gap", AVOID via per-point strong-minor charts; `routeverify`: "Brick F likely DROPPABLE" |
| **Rank-r codim integrability (D-B)** — `RouteMSJRankRCodim`, `lintegral_cube_frobSq_neg_of_finrank_range` | endgame | 2026-07-13 | rank-stratum codim of `frobSq^{−c'}` | **Partly** — repro's `Mval(t)=codim S(t)` is the codim; the *integrability* is new | **Survived (as atom)** — general rank-strata statement; consumed by both route-B and incidence |
| **Schur-complement identities** — `RouteMSchur*` (109-file SJ family root), `Core.SchurChartIff`, block-LU rank identity | repro (Lemma 2 block-elim) 06-24 | 2026-06-25 (`RouteMSchur`) | block elimination / Schur reduction of the node loss | **Yes** — repro §"Block elimination (Lemma 2)" | **Survived** — `chart5recon`: block-LU rank identity "ALREADY BANKED in Core.SchurChartIff"; used by chart 5 |
| **Determinantal minor charts + big-cell blow-up (the incidence family)** — `RouteMSJIncidenceChart`, `…Exponent`, `…Chart4Polar`, `…Gluing`, `…Chart5BigCell` | **repro (the L=2 incidence chart), 06-24** | **2026-07-14 22:43 → 07-15 01:04 (one night)** | thresholdhunt DEGRADES ⟹ shell/coupling load-bearing ⟹ incidencepp designs the coupled resolution | **Yes** — repro names the chart `A=α[[1,a],[b,ab+δ]]` + blow-up `{δ=u=v=0}` explicitly | **On the final (verified) route** — `routeverify`: coupled incidence-direct is the required route |
| **Null-overlap gluing** — `RouteMSJIncidenceGluing`, `lintegral_lt_top_of_finite_cover`, `RouteMNullSliceCov` | endgame | 06-30 (NullSliceCov); 07-15 00:51 (Gluing) | finite-atlas coverage of the box up to null | **Partly** — repro's atlas/cover idea; the generic engine is new | **Survived** — atlas-parameterised (bltj-robust); on the final route |
| **Reversal CoV (waist)** — `RouteMSmearedWaist`, `WaistReversalCoV`, `deepTailMin_rev_le_of_waist` | endgame | 07-02 (SmearedWaist) | M₂>M₁ / hpiv-failing cuts route to the waist | No — dispatch-architecture-emergent | **Survived** — `routeverify` CHECK 1: waist connector-wired, routes hpiv-failing cuts |
| **Cauchy-Binet / PSD-mono / AM-GM atoms** | earlier expeditions | pre-fork (Core) | generic PSD/minor algebra | **Yes** — generic linear algebra | **Survived** — domain-general, route-independent |

Reactive-build timeline (module first-adds, the "brick-by-brick" signature): `GeneralR1Recursion`
06-21 (per-node squeeze route) → `RouteMLayerCover` 06-24 (cover route) → `RouteMNullSliceCov` 06-30 →
`RouteMSmearedWaist` 07-02 (smeared route) → `RouteMSJResolution` 07-06 (the SJ / Schur-Jacobian route
opens). The SJ family then **exploded**: 2 (07-06), 13 (07-07), 11 (07-08), 26 (07-10), 23 (07-11),
10 (07-12), 19 (07-13) = 104 modules in 8 days, then 1 (07-14, incidence) + 4 (07-15). 499 Validate
modules total; 109 `RouteMSJ`, 222 other `RouteM`.

---

## 2. Predictability against the June reproduction

**FACT.** The reproduction (`theory/aoyagi-2023-reproduction/`, `aoyagi-2023-worked.tex`) is dated
2026-06-23/24, i.e. it predates the fork (06-25). A reader on 06-25 had it in hand. Its §"Proof, part
II + III" lays out Aoyagi's proof as an explicit chart tower and **names every general move that
carried the endgame**:

- **Block elimination (Lemma 2)** — unit transforms → the Schur family (`RouteMSchur`, landed 06-25).
  Repro §"Block elimination (Lemma 2)".
- **Recursive blow-up with monomial Jacobian** — "Each exceptional divisor `u_{s,k}` carries Jacobian
  power `M_{s,k}−1`… the change-of-variables determinant is `∏ u_{s,k}^{M_{s,k}−1} du_{s,k}`" (worked.tex
  §blowup, "The Jacobian"). → the radial/polar CoV family.
- **Per-divisor bookkeeping / Newton-polytope threshold read** — the `diag(b)` invariant, `rlct_core =
  ½ min{M_{s,k}}` boxed formula.
- **The incidence chart, explicitly** — "the L=2 incidence chart `A=α[[1,a],[b,ab+δ]]`,
  `B=[[u−ar,v−as],[r,s]]`, then one blow-up of `{δ=u=v=0}`" (worked.tex, R1 design verdict). This is the
  literal object `RouteMSJIncidenceChart` realises.

**The decisive quote (predictability of the *route*, not just the tools).** The reproduction did not
merely name the incidence machinery — it **adjudicated the route and refuted the decoupled alternative**,
in `verify-r1-light-recursion.md` (2026-06-23) and worked.tex §candidates "The light-vs-coupled fork —
RESOLVED":

> "A *threshold-only* invariant … is **provably insufficient**. It is faithful only when every
> binding-branch peel has corank ≤ 1 … It **BREAKS at corank ≥ 2** … a per-row multiplicity cannot
> encode *which* divisor variables are SHARED, and sharing changes the Newton polytope hence the RLCT."
> … "**R1 Lean shape — DECIDED: option (ii), the coupled diag(b) recursion.**"

and the certified binding witness `(3,3,4)`, `t=(1,0)`, corank `(2,2)`, `rlct=4` vs the decoupled `3`
(`verify-r1-diagb-334.md`, "PROVED + decorrelated Codex + Aoyagi–Watanabe 2005 anchor").

**Interpretation.** The general machinery that the verified final route calls for — Schur block-elim,
recursive blow-up / radial CoV, and above all the **coupled** determinantal-incidence resolution — was
not just predictable on ~06-25; it was **explicitly named and the route explicitly decided** in the June
reproduction. The one principle the endgame most needed — *the coupling is essential; a decoupled model
breaks at corank ≥ 2* — is the reproduction's headline conclusion.

**Genuinely NOT predictable (Lean-architecture-emergent):** (i) the measurable-eigenframe machinery
(Brick F) and its Mathlib gap — an artefact of trying to do a *global* frame in Lean, avoidable by
per-point charts; (ii) the box-integrability *thresholds* for the corank-Gram and rank-r integrals
(`a<m−b+1`, `2q>N`) — real analysis emergent from the Lean integrand, though their *shape* follows the
codim; (iii) the waist-reversal dispatch — a bookkeeping device for the general-M driver, not in Aoyagi;
(iv) the entire off-shell "deep-floor" apparatus (Ky-Fan floor, `shellSpine_le_hsQ_box`,
`pivotDomLHS_full_lt_top`, `frobSqBlockFull_lt_top`, `stackedGram_flagPeel_le`) — emergent from a route
*that the reproduction had already argued could not work*.

---

## 3. Route-survival and the generality dividing line

The endgame ran a long chain of routes, tracked in `endgame-lanes.md`. The spine:

- **07-06 → 07-13:** the SJ route builds an **off-shell, decoupled, "full-block via deep floor"**
  apparatus (104 modules). Sub-routes, each isolating "the last hard brick" and each superseded:
  `cruxfin` (shell-0 only) → `t2adjud` (OBSTRUCTION: `shellSpine_le_hsQ_box` FALSE for j≥1) → `pradial`
  → `finfin` (isolates the shear-CoV wall) → `shearfin` (`frobSqBlockFull_lt_top`) → `wallfin` ("LABOUR
  not Mathlib-wall; hardest brick = `stackedGram_flagPeel_le`") → `flagpeel`.
- **07-14 `thresholdhunt` — the decisive catch** (`endgame-lanes.md:108`): `frobSqBlockFull_lt_top` is
  **FALSE as stated** (witness `(6,6,6)`, u=4, c'=13.75). "the divergence is at the OFF-SHELL
  low-rank-W locus … the **shell σ_min(hsQ)≥ε WOULD exclude it** … the shell is LOAD-BEARING; the deep
  floor is NOT a substitute; the whole 'off-shell full-block via deep floor' strategy
  (t2adjud→pradial→finfin→shearfin→flagpeel) is the GAP." Re-scope to the **shell-restricted coupled
  residual = step2's OBSTACLE-A, the hard piece the full-block detour was AVOIDING**.
- **07-14 night:** `incidencepp` designs the coupled incidence resolution (consuming thresholdhunt +
  couplingfin verdicts); `brickdbuild`/`brickdcont` build the 5 incidence modules **in ~2.5h**.
- **07-15:** route-fork churn — `capstonerecon` (full-block tower, dead) → `routefork` (route-B
  S3/deep-floor) → **operator LATE-4 catch** (route B BROKEN: "the coupling is ESSENTIAL = exactly what
  the incidence machinery was built for", `endgame-lanes.md:56`) → `routeverify` (coupled
  incidence-direct VERIFIED; route B dead; Brick F droppable).

**Classification.**

- **(i) Survived every route change / on the final route** — all are *statements about a matrix integral
  or a matrix identity per se*: radial/polar CoV (`RouteMSJRadialPolar`, `pivotBlock_radial_blowup`),
  det-Gram/Wishart corank integrability (`detGram_lintegral_box_lt_top`), rank-r codim integrability
  (`RouteMSJRankRCodim`), spectral `frobSq = Σλ` (`RouteMSJFrontSpectral` — `wallfin`: "IS glue (i)"),
  Schur block-LU rank identity (`Core.SchurChartIff`), σ_min↔det bridge (`RouteMSJProductTube`),
  null-overlap gluing engine, Cauchy-Binet/PSD/AM-GM. `wallfin` (07-14) inventories these as "ALL
  analytic primitives BANKED sorry-free."
- **(ii) Banked-but-superseded** — all are *statements coupling several route objects*, or route-specific
  floors: `shellSpine_le_hsQ_box` (couples shell-indicator + pivotShell + hsQ; FALSE for j≥1),
  `pivotDomLHS_full_lt_top` / `frobSqBlockFull_lt_top` (couple full-box + deep-floor + threshold; the
  latter FALSE), `stackedGram_flagPeel_le`, the Ky-Fan deep-factor floor (`RouteMSJKyFan`,
  `shell_subset_goodSet`), the full-floor pivotShell tower, and **Brick F** (`RouteMSJMeasurableEigendecomp`,
  2 `sorry`; "likely DROPPABLE"). Note: the Ky-Fan and rank-r *atoms* are general; what died is the
  *floor assembly* that consumed them.
- **(iii) Died outright** — the decoupled "light" recursion (refuted at *design*, June, never built in
  Lean); route-B's constructive S3 floor (`hpiv` false on M₂>M₁; A_cor-coupling type error).

**The pattern (interpretation, strongly supported).** Survival correlates almost perfectly with
**domain-generality**. A lemma phrased as "this matrix integral / this determinant-rank identity has this
value" survived every route change, because its truth does not depend on how the route couples its
objects. A lemma phrased as "on *this shell*, *this pivot block* dominates *this comparator* under *this
floor*" died the moment the route's coupling assumption was falsified — and the falsifications
(`t2adjud`, `thresholdhunt`) were all the *same* error: **dropping a coupling the geometry does not
permit dropping**, i.e. the exact `corank ≥ 2` phenomenon the June reproduction had already isolated.
"Safe to build" = the statement is true independent of the route = it is about a matrix integral, not
about a relation between route-specific objects.

---

## 4. The counterfactual

**Setup.** Suppose on ~2026-06-25 (fork day, reproduction complete) the expedition had commissioned, in
parallel and *route-independent*, the Aoyagi-implied library toolkit:

- **Tide A — matrix polar/radial CoV** (blow-up Jacobian `u^{M−1}`, radial `‖·‖²`-monomial reduction).
- **Tide B — determinantal minor charts + rank-strata integrability** (the incidence charts, big-cell
  blow-up over `SchurChartIff`, det-Gram/Wishart corank integral, rank-r codim integral).
- **Tide C — measurable frames** (eigenframe / ordered-roots-measurable).

**How much of the 07-13→15 grind would have been prefabricated?**

- **Tide A + Tide B: essentially the entire reusable analytic engine of the endgame.** Every family in
  survival-class (i) is exactly what these two tides produce. The **existence proof is in the record**:
  the determinantal-incidence family (5 modules — `RouteMSJIncidenceChart`, `…Exponent`, `…Chart4Polar`,
  `…Gluing`, `…Chart5BigCell`) was built **and fidelity-reviewed in one night** — first add
  22:43 (07-14), last add 01:04 (07-15), chart-5 fidelity PASS 01:24 — *once commissioned*, over an
  algebraic core (`SchurChartIff`) that was **already banked in Core** (`chart5recon`: "block-LU rank
  identity ALREADY BANKED sorry-free"). These charts are per-stratum CoV statements that are TRUE
  regardless of the route ("each chart is an INDIVIDUAL CoV lemma, TRUE regardless of bltj", `endgame-lanes.md:28`);
  nothing about them needed the route settled first. They waited until 07-14 **only because the
  expedition was pursuing the off-shell detour** — a detour the reproduction had argued against.

- **Tide C: mostly wasted.** Brick F hit a genuine Mathlib gap (2 `sorry`), was routed around by
  per-point strong-minor charts (`wallfin` trap #1), and is "likely DROPPABLE" (`routeverify`). A
  route-independent frames library would have been built and then shelved.

**What no library could prefabricate:** the *route adjudication* — the decision that the shell-restricted
coupled residual (not the off-shell full-block) is the sound route. But — and this is the sharpest
finding — **that adjudication was already in the reproduction** ("R1 must carry the coupled diag(b)
support", 06-24). The endgame's ~8 days of decoupled building (07-06→07-13) and its two soundness
catches (`t2adjud`, `thresholdhunt`) were, at the level of principle, **re-deriving the June
conclusion** in the specific setting of `headSplit_domination`. (Fair caveat: the June adjudication was
about the *core* recursion / `resolution_charts` gate; the endgame's object is the *head-split
domination* for the general-M box-threshold. These are distinct lemmas sharing one principle — coupling
cannot be dropped at corank ≥ 2 — so the reproduction's verdict was *directly transferable*, not
*literally identical*.)

**Net counterfactual verdict.** A June-25 commission of Tide A + Tide B (matrix CoV + determinantal
charts / rank-strata integrability) would have prefabricated the great majority of the reusable July
endgame analytic engine, and — because those charts are the *coupled* resolution — would have kept the
expedition on the route the reproduction had chosen, plausibly bypassing the off-shell full-block detour
(the `pradial→finfin→shearfin→flagpeel→wallfin` chain of ~104 modules and two false-sorry near-misses).
Tide C would have been largely wasted effort. The honest cost of *not* building proactively: the
reproduction's route decision was allowed to lapse, a decoupled route was built at scale, and it took
two decorrelated soundness gates (each correctly firing) to walk it back to the coupled route the paper's
own structure dictates.

---

## 5. Quiver / orbit-engine overlap (Task 5)

**FACT (imports at `f483692ef`).** The RLCT/DLN modules import **no** quiver/orbit/Kostant/Gabriel
machinery — a grep for those names in `import` lines returns nothing. They *do* import Core's **outputs**
of that engine as numbers: `Core.CTheta`, `Core.CThetaPermInvariance`, `Core.CThetaThetaBridge`,
`Core.CThetaQIPConverse` (1× each), and Core's **matrix-rank tools**: `Core.Matrix.RankNormalForm` (4×),
`Core.SchurChartIff`, `Core.ResidualRank`, `Core.RankLocusClosed`, `Core.Matrix.GramFullRank`,
`Core.SchurProductFactor`, `Core.CommonPivotL2`, `Core.CascadeAchiever`.

**Interpretation.** There is **no code duplication** and only a thin, deliberate *conceptual* seam. The
type-A quiver engine (dev branch, earlier expeditions) stratifies the *variety* — the zero-product /
rank-r loci of the matrix product — by orbits ↔ Kostant partitions, and computes the algebraic
codimension `C = minAdm` (the Ext codimension). The endgame's shell/corank/sector apparatus stratifies
the *integral* — the domain of `∫ frobSq^{−c'}` — by singular-value shells and corank strata. These are
different objects (an algebraic variety stratification vs a measure-theoretic domain decomposition); they
**meet at exactly one number**, `minAdm`, which both compute and which the exponent-gate cross-check
(`endgame-lanes.md:18`, "incidence resolution and the independent codim certificate agree on WHY T1 is
the threshold") treats as a bedrock consistency check, not a shared construction. The shell stratification
is therefore not re-implementing the quiver orbit-stratification; it re-uses the quiver engine's *scalar
verdict* and Core's *rank-normal-form* lemmas, and stratifies a different space for a different (analytic)
purpose.

---

## Facts vs interpretation — summary separation

**Facts:** all dates, SHAs, module/`sorry` counts, import lists, and the quoted reproduction/ledger
passages above. The incidence family's one-night build window (07-14 22:43 → 07-15 01:04, fidelity PASS
01:24). Brick F has 2 `sorry`. `frobSqBlockFull_lt_top` and `shellSpine_le_hsQ_box` (j≥1) were proved
FALSE (thresholdhunt, t2adjud, both with concrete witnesses + decorrelated Codex). The expedition is
unclosed at the fork (mint still `sorry`-gated).

**Interpretation:** the generality dividing line (survival ⇔ domain-generality); that the endgame
re-derived the reproduction's coupling verdict; the counterfactual magnitudes (Tide A+B ≈ the reusable
engine; Tide C ≈ wasted). These are inferences from the facts, well-supported but not machine-checked.
