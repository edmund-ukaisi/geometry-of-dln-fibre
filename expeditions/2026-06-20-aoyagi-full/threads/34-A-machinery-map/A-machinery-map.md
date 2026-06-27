# A-machinery map — what (A) infrastructure already exists on `expedition/aoyagi-full`

Thread 34 (scout, read-only recon). Branch `expedition/aoyagi-full`, HEAD `9b439a46`. The mission is the
FULLY GENERAL `aoyagi_learning_coefficient`. This maps the existing machinery against the four headline
gates so the controller charges the remaining general builds without re-deriving banked work.

Method: aggregator transitive-closure computed from `lean/DLNFibre.lean`; real open-`sorry` count via the
script's own comment-aware counter (matches `scripts/sorries` total = **13**); reverse-dependency graph for
gate-coverage. All file:line facts verified in-code, not inferred.

---

## 0. Headline numbers (corrects the brief's estimate)

- Validate `.lean` files tracked: **97**. GATED (in the aggregator's transitive closure): **34**.
  UNGATED (escape the green-gate): **63**. (The brief's "25 of 97 / ~72 escape" was an undercount of the
  gated set; the real split is 34/63. Total modules under `DLNFibre/`: 184 → 106 gated / 78 ungated.)
- **Real open sorries: 13 total** (verified, NOT docstring mentions): **5 INSIDE the gate**, **8 escape**.
  - INSIDE the gate (gate is green-*with-sorries*, the 4 headline gates + 1 R1 atom):
    `Skeleton.lean` ×4 (1131, 1177, 1234, 1707) + `RouteMLayerCoverGE.lean` ×1 (133).
  - OUTSIDE the gate (the ungated frontier):
    `DeepestGaugeConstruction.lean` ×4 (2915, 3118, 3123, 3289) + `DeepestGaugeChart.lean` ×1 (403)
    + `RouteMSchur.lean` ×2 (164, 284) + `RouteMRecursion.lean` ×1 (257).
- Of the 63 ungated Validate files, **59 are sorry-free** (proven but unprotected) and only **4 carry open
  sorries** (the genuine frontier). The huge ungated count is mostly *proven* machinery escaping the gate,
  not WIP.

---

## 1. Inventory by gate

### Gate L2 — the gauge-chart producer / deepest-point minimiser (`Deepest*` subtree)

Skeleton target: `rlctAt_deepest_le_of_optimal` (Skeleton:1177, GATED sorry).

The `Deepest*` subtree is **30 files, ALL UNGATED**, of which **28 are sorry-free** and **2 carry the L2
frontier**:

| file | gate | open sorries | role |
|---|---|---|---|
| `DeepestGaugeConstruction` | UNGATED | **4** (2915, 3118, 3123, 3289) | the L2 ROOF — pulls ~25 Deepest* files. 2915 = L=2 diffeo arm; 3118/3123 = L≥3 interior `hinterface`; 3289 = L≥3 grouped-G0 diffeo |
| `DeepestGaugeChart` | UNGATED | **1** (403) | `Nonempty (DeepestGaugeChart …)` — the chart-existence sorry; also **hosts the `continuous_dlnLoss` clash** |
| 28 other `Deepest*` | UNGATED | 0 | sorry-free L2 support (frames, Schur peel, split-smooth, IFT, telescoping, diffeo bridge, …) |
| `DeepestMinRlct` | UNGATED | 0 | **D1 ≥-leg content** — proves `deepest_le_of_optimal_via_L2`; the prerequisite for Skeleton:1177 (still needs the full-`B` wire-through-L2) |
| `DeepestNormalFormWiring` | UNGATED | 0 | conditional closer `deepest_normal_form_of_value` — a one-line fill of the Skeleton value sorry once L2+R1 land |
| `DeepestCoreNonvanishing` | UNGATED | 0 | `hMid ⟹ hGne` bridge (reduced core ≠ 0 a.e. from `0 < M s`) |

**L2 frontier = 5 sorries in 2 files.** The rest of L2 is built and proven.

### Gate R1 — resolution charts (`resolution_charts`, Skeleton:1234, GATED sorry)

R1 splits into a LOWER leg (box-divergence `≤`) and an UPPER leg (finiteness `≥`/`hfin`), plus a
carrier-migration blocker.

**R1 LOWER leg — ONE open sorry, GATED:** `routeMCore_box_diverges_achiever` (`RouteMLayerCoverGE.lean:133`).
This is discharged the instant `NodeAchieverChart M` can be INHABITED for arbitrary `M`. The M-agnostic
divergence ASSEMBLY (`routeMCore_box_diverges_of_nodeChart`, `NodeAchieverChart.lean:171`) is already
proven sorry-free and GATED; only the per-M *producer* is missing.

- GATED, proven (the lower-leg banked engine + assembly):
  - `NodeAchieverChart` (structure + `nodeChart_thresholdLe` + `nodeLeaf_box_div` + the assembly) — GATED.
  - `RouteMAchieverTelescope` (`Chain.chain_telescope`, `chain_telescope_zero`) — GATED, axiom-clean.
  - `RouteMAchieverGeneralDet` (`general_composed_clm_abs_det`, `listProd_clm_abs_det`) — GATED, axiom-clean.
  - `RouteM4422` / `RouteM3333` / `RouteM3333Atom` (the two concrete inhabited charts) — GATED.
  - `RouteMLayerSplit` / `RouteMLayerValue` / `RouteMLayerCover[GE][GEL2]` (the layer-collapsing carrier
    `minAdmRec_eq_minAdm`, the cover) — GATED.
- UNGATED, R1-lower related: none of the lower-leg producer pieces are ungated — the lower leg's only open
  work is the single GATED sorry + the in-flight per-M `Chain` block construction (tasks #74–#80).

**R1 UPPER leg — UNGATED frontier:**
- `RouteMSchur.lean` ×2 sorries (164 = the N2 two-sided Schur comparison `c₀·(…) ≤ frobSq ≤ c₁·(…)`;
  284 = `routeMCore_threshold_lt_top`, the depth-`r` WellFounded-on-corank measure recursion — flagged the
  HIGH-risk long pole). UNGATED.
- `RouteMRecursion.lean` ×1 sorry (257) — the carrier-migration blocker: `RouteStep`/`routeStep`/`routeAtlas`
  must migrate off the fixed-arity `ChainDimSplit M` onto `RouteMLayerSplit.routeLayerAtlas` (the genuine
  machinery is sorry-free in `RouteMLayerSplit`; this is controller-gated staged surgery, not a leaf fill).
  UNGATED.
- Sorry-free UNGATED upper-leg / value-fold support: `RouteMValue`, `RouteMNReg`, `RouteMBranch`,
  `RouteMBranchRead`, `RouteMClassify`, `RouteMScaffold`, `RouteMNodeDescent[Build]`, `RouteMO1Bridge`
  (SCOPE-LIMITED, soundness caveat in-file), `SchurState`(GATED)/`SchurNodeAssembly`, `RouteMGeneralAssembly`,
  the `Binding*` trio, `MinAdmMono`, the `Case*RouteStep` anchors (222/323/334), `RouteM334Hfin/Ratiofin`,
  `RadialResidualPower`, `FrontPivot{Producer,WLOG}`, `LossHomogeneity`, `NodeHomogeneity`.

### Gate D1 — local→global assembly + value (Skeleton:1131) and the HEADLINE

- `rlctAt_deepest = (r·(H0+HL−r))/2 + lambdaCore(H−r)` (Skeleton:1131, GATED sorry) — the deepest-point
  RLCT value (D1 value + the `½·minAdm = aoyagiLambda` identification).
- `aoyagi_learning_coefficient` (Skeleton:1725) — the headline; assembles D1 ▸ L2 ▸ R1 ▸ S2 ▸ A1. Its proof
  body is currently the assembly stub over the gated sorries.
- `aoyagi_rrr` (`RRR.lean:89`) — the L=2 / reduced-rank-regression instance; GATED, proven-conditional
  (carries `sorryAx` transitively, clean modulo the cited `monomial_rlct` S2 axiom at the (2,2,2) anchor).
- `aoyagiTheta_eq` (Skeleton:1707, GATED sorry) — the SECONDARY θ deliverable (optional; not on the
  headline critical path).
- D1-feeding UNGATED machinery: `DeepestMinRlct` (≥-leg), `DeepestNormalFormWiring` (value closer),
  `MvalMultSum` (the combinatorial `Mval = codimForm` tie via `cascadeRank` — the headline
  value-identification piece), `CascadeAchiever` + `RouteMAchieverForce` (rank-pattern realizability).

---

## 2. The R1-general achiever lower-atom — does existing machinery feed the chart build?

**Verdict: the chart construction (`phi_M`, `leafH`, `det`) is GEOMETRICALLY INDEPENDENT of the
combinatorial cascade/achiever machinery. It should build ON the two banked algebra engines, NOT on
`CascadeAchiever`/`RouteMAchieverForce`/`RouteMBranchRead`/`Binding*`/`routeLayerAtlas`.** (Codex `xhigh`
corroborated, decorrelated.)

Evidence (verified in `RouteM4422.lean` and the `RouteM3333` pair — the two sorry-free inhabited charts):
the chart's `phi`, `leafH`, and `|det Dφ|` are built from PURELY GEOMETRIC inputs —
- a Schur-frame CLM (`Q4422CLM`) ∘ a radial blow-up on the deepest active factor (`pb4422`,
  `pivotBlowupOnDeriv_det`), with the radial exponent `= active.card − 1 = minAdm − 1`;
- `leafH p = minAdm M − 1` on the single binding pivot, `0` on spectators;
- `det = u_p^(minAdm−1)`.

They do **NOT** reference `achieverRankPattern`, `cascadeTuple`, or `RealizesAchiever`. The only
combinatorial input the chart needs is the scalar `minAdm M` (and which factor carries the achiever center).

**What the chart build SHOULD reuse (already GATED, axiom-clean):**
- `Chain.chain_telescope` / `chain_telescope_zero` (`RouteMAchieverTelescope`) — supplies the global
  factorization `prod M (φ_M u) = u · H` from per-level local identities `C_s·A_s = B_s·C_{s+1} + u·E_s`,
  `C_n = u·R`. The per-M block construction (tasks #75/#76) must produce a `Chain` *instance*; the
  telescope is proven once.
- `general_composed_clm_abs_det` (`RouteMAchieverGeneralDet`) — supplies `|det Dφ_M| = ∏ per-factor-det`
  for the variable-length `List.prod` chart, with no `Fin (r−j)` cast fight (task #77).
- `NodeAchieverChart` structure + `routeMCore_box_diverges_of_nodeChart` assembly + `nodeChart_thresholdLe`
  — the consumer contract (task #80 = inhabit the structure, then `exact` the assembly).

**What the chart build should NOT touch (a different layer — the value-fold / upper-leg):**
- `CascadeAchiever.rankFn_cascadeTuple_eq_achieverRankPattern`, `RouteMAchieverForce.RealizesAchiever`,
  `RouteMBranchRead` — these produce the achiever RANK PATTERN and the binding `T*` realizability; they
  feed the value-side identification, not the analytic chart.
- `BindingSpine`/`BindingRecursion`/`BindingArith` — the binding RLCT-recursion skeleton (upper-leg /
  value path), not the chart.
- `RouteMLayerSplit.routeLayerAtlas` — the layer-collapsing carrier for the routeStep MIGRATION (upper-leg
  / value-fold), not the lower-leg chart.

**The one place the cascade/achiever tie IS load-bearing (so it is not orphaned):** the HEADLINE
value-identification `½·minAdm = aoyagiLambda`, via `MvalMultSum` (`Mval M T = codimForm(cascadeRank M T)`,
the paper's "new content" tie) + `CascadeAchiever`/`RouteMAchieverForce` (forcing the binding `T*` to
genuinely realize the achiever stratum so the threshold equals `minAdm`, not a vacuous `∃`). This is the
upper-leg / D1-value seam, NOT the lower-leg chart. So: lower-leg chart builds on the algebra engines; the
cascade tie surfaces at the headline value-fold. **The controller must not duplicate the cascade/achiever
machinery inside the chart producer.**

---

## 3. Gate-coverage hygiene

### (i) LOAD-BEARING for the general headline — should be wired into the gate to be protected

These are sorry-free, terminal, and feed a gate's eventual proof. They escape the green-gate today (a
green build does not protect them; a future edit could silently break them). They are the "roofs" of their
clusters (no in-repo importer) and are the right wire-in points:

- **L2:** `DeepestGaugeConstruction` (the roof — once its 4 sorries close, wiring it pulls ~25 sorry-free
  Deepest* files into the gate in one import). Plus the standalone L2/D1 sinks `DeepestMinRlct`,
  `DeepestNormalFormWiring`, `DeepestCoreNonvanishing`, `DeepestEFullSregComparability` (not imported by
  the construction roof — separate sub-results that also need explicit wiring).
- **R1 upper / value-fold:** `RouteMGeneralAssembly` / `RouteMScaffold` (the general routeStep assembly
  roofs), `RouteMSchur` (once its 2 sorries close), `BindingSpine` (the binding recursion roof), the
  `Case*RouteStep` anchors.
- **D1 value tie:** `MvalMultSum`, `CascadeAchiever`, `RouteMAchieverForce`.

### (ii) WIP toward (A) — the real frontier (carry roadmapped sorries)

`DeepestGaugeConstruction` (4), `DeepestGaugeChart` (1), `RouteMSchur` (2), `RouteMRecursion` (1). These 4
files hold all 8 ungated open sorries. Every one is recent (2026-06-22..06-25) and roadmapped in the
synthesis (L2 interior; the corank recursion; the carrier migration). None is stale.

### (iii) SUPERSEDED / scratch — should be deleted

**None found.** All 63 ungated files were last touched 2026-06-22..06-25 (this expedition), and every
header read describes a deliberate, terminal result — including the ones that *look* redundant
(`Case222RouteMValidation` is a labeled (2,2,2)-through-the-general-engine MILESTONE; `RouteMO1Bridge`
carries an explicit in-file SCOPE-LIMITED soundness caveat but is a real result; `DeepestEFullSregComparability`
documents that its atoms moved upstream to `FrontPivotProducer` but is "kept" deliberately). Recommend the
controller spot-check `RouteMO1Bridge`'s caveat at wire-time rather than delete.

### Gate leaks

**Zero gate leaks.** No GATED module imports an UNGATED one (verified over the full closure). The gate is
internally consistent; the ungated set is genuinely outside the build's transitive closure, not leaking in.

### Name clashes — the gating blockers (the brief's verification, with a CORRECTION)

The synthesis flagged `continuous_dlnLoss` as the L2 gate-close blocker. **It is NOT the only blocker.**
Two real same-namespace (`DLNFibre.DLN.RLCT`) clashes block wiring the Deepest* subtree:

1. `continuous_dlnLoss` — `DeepestGaugeChart.lean:161` (UNGATED) vs `Foundations/LossContinuity.lean:52`
   (GATED). Same signature; fatal once `DeepestGaugeChart` enters the aggregator. (Synthesis-known.)
2. **`frobSq` + `frobSq_nonneg`** — `DeepestSchurComparability.lean:49/53` (UNGATED, `X : Matrix m n ℝ`) vs
   `MatMulFibre.lean:33/37` (GATED, `M : a → b → ℝ`). DIFFERENT signatures, SAME name, SAME namespace —
   a fatal duplicate-definition / ambiguity once both are in the build. `DeepestSchurComparability` does
   not currently import `MatMulFibre`, so it is latent today; it bites at L2 wiring. **NOT flagged in the
   synthesis** — surface to the controller.

Plus the value-side clash already in the synthesis: `minAdm_M4422` — `Case334RouteStep.lean:161` (UNGATED)
vs `RouteM4422.lean:52` (GATED). Bites when `Case334RouteStep` is wired.

So the L2 gate-close has **two** dedupes (`continuous_dlnLoss`, `frobSq`/`frobSq_nonneg`), not one; the R1
value-side wiring has one (`minAdm_M4422`).

---

## 4. Recommended (A) build sequence (a recommendation; the controller decides)

The controller is mid-flight on the R1-LOWER chart producer (tasks #74–#80, #76 in_progress). Two
considerations pull in different directions: Codex `xhigh` recommends doing the routeStep/atlas migration
FIRST (so the high-risk R1-upper recursion is not built against the wrong carrier) and probing R1-upper
EARLY (it is the long pole); the harness disposition ("fill the layer — completion is your strength")
favors finishing the in-flight, independent, low-risk lower-leg piece before opening a new front. Both
agree the lower leg is self-contained and the upper-leg recursion is the riskiest piece. My synthesis:

1. **Finish R1-LOWER `NodeAchieverChart M` (in flight, #75–#80).** Self-contained, low-risk, builds on the
   two GATED algebra engines + the GATED assembly. Closes the GATED sorry `routeMCore_box_diverges_achiever`
   (RouteMLayerCoverGE:133). Highest-value next increment: it removes a gate-internal sorry. Do NOT pull in
   cascade/achiever machinery (§2).
2. **Probe R1-UPPER early (cheapest discriminating test BEFORE the full build).** Codex's probe: after a
   minimal routeStep/atlas migration, prove the FIRST nontrivial recursive descent lemma on a generic
   positive-corank route and check the induction measure / atlas domains / Schur-finiteness hypotheses line
   up. This surfaces a carrier/domain mismatch before sinking the full `routeMCore_threshold_lt_top`
   (RouteMSchur:284) recursion — the HIGH-risk long pole (the single most likely hidden wall).
3. **routeStep/atlas migration (RouteMRecursion:257) + R1-UPPER recursion (RouteMSchur:164, 284).** The
   migration is the sequencing TRAP (Codex): R1-upper "looks ready" but its controller is on the fixed-arity
   carrier; migrate to `routeLayerAtlas` first. Then the corank recursion. Reuse the sorry-free
   `RouteMLayerSplit` machinery; do not re-derive it.
4. **Wire R1 closed → `resolution_charts` (Skeleton:1234).** With both R1 legs sealed, the atlas
   `= ⨅ monomialThreshold` closes. Wire `RouteMGeneralAssembly`/`RouteMScaffold` into the gate at this point
   (dedupe `minAdm_M4422` first).
5. **L2 frontier (DeepestGaugeConstruction ×4 + DeepestGaugeChart ×1).** Independent of R1; can run in
   parallel with steps 1–4 (different files, no conflict). On close, wire `DeepestGaugeConstruction` into the
   gate — but FIRST dedupe BOTH `continuous_dlnLoss` AND `frobSq`/`frobSq_nonneg` (§3), else the wire fails.
   This pulls the 28 sorry-free Deepest* support files into the gate in one import (large coverage win).
6. **D1 assembly + value (Skeleton:1131, 1177).** With L2 + R1 sealed: wire `DeepestMinRlct` (≥-leg) through
   L2 to close 1177; use `DeepestNormalFormWiring.deepest_normal_form_of_value` to one-line-close the value
   sorry. This is where `MvalMultSum` + the cascade tie become load-bearing (the `Mval = codimForm`
   identification).
7. **Headline `½·minAdm = aoyagiLambda` (Skeleton:1725).** Value-identification glue — do LAST, after D1/L2/R1
   are sealed (Codex: doing this early is useless until R1's threshold theorem is real).
8. **θ secondary `aoyagiTheta_eq` (Skeleton:1707).** Optional; off the critical path; last or deferred.

**Dedupe/wire/delete summary for the controller:**
- DEDUPE (before L2 wiring): `continuous_dlnLoss` (DeepestGaugeChart ↔ LossContinuity) AND `frobSq`/
  `frobSq_nonneg` (DeepestSchurComparability ↔ MatMulFibre — synthesis-MISSED). Before R1 value wiring:
  `minAdm_M4422` (Case334RouteStep ↔ RouteM4422).
- WIRE (as each gate closes, to protect 59 sorry-free escapees): the cluster roofs
  `DeepestGaugeConstruction`, `RouteMGeneralAssembly`/`RouteMScaffold`, `BindingSpine`, plus the standalone
  D1/L2 sinks `DeepestMinRlct`, `DeepestNormalFormWiring`, `DeepestCoreNonvanishing`, `MvalMultSum`,
  `CascadeAchiever`, `RouteMAchieverForce`.
- DELETE: nothing (no superseded scratch found). Spot-check `RouteMO1Bridge`'s in-file SCOPE-LIMITED
  soundness caveat at wire-time.

---

## Reflection

- Most likely to ADVANCE the expedition: closing the R1-LOWER `NodeAchieverChart M` producer (step 1) — it
  is in flight, self-contained, builds on two already-banked GATED engines, and removes a gate-internal
  sorry. The completion-is-strength move.
- Most likely to BREAK: R1-UPPER `routeMCore_threshold_lt_top` (RouteMSchur:284), the depth-`r`
  WellFounded-on-corank measure recursion — the explicitly-flagged long pole, compounded by the routeStep
  carrier migration it depends on. Probe it early (step 2) before committing the full build.
- Next computation that would clarify: run Codex's R1-upper probe — a single generic positive-corank
  descent lemma on the migrated atlas — to confirm the induction-measure / atlas-domain / Schur-finiteness
  hypotheses line up before the recursion is built. That is the cheapest test that would surface the one
  hidden wall on the (A) path.
