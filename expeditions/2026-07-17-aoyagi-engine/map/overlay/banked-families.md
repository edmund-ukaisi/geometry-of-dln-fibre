# Overlay — banked-family cards (cartographer, curated layer)

*The banked substrate the engine CONSUMES (never rebuilds — "survey before commissioning", compass
standing counsel). **Pass #2 (2026-07-18): REFRESHED + CONSUMPTION-SCOPED by the remaining rungs
R1–R6** (recon cert §5 roadmap). Each rung lists the families it consumes with PINNED decl names,
`file:line`, sorry-status, and an import-weight note. Pins RE-VERIFIED by grep against the live tree
(2026-07-18); drift from pass #1 flagged inline. All paths `lean/DLNFibre/DLN/RLCT/…`.*

**Import-weight key** (transitive DLNFibre-internal import count, a build-cost proxy; measured
2026-07-18): LIGHT ≤ 40 · MEDIUM 40–150 · HEAVY > 150. The full whitelist + the heavy-cone re-home
is in [[import-hygiene]].

**Rung → hole map.** R1/R2 discharge `monomialization_terminates` (`EngineObligations.lean:182`,
sorry `:184`); R3 discharges `region_glue` (`EngineObligations.lean:244`, sorry `:248`); R5 flips
`engine_box_threshold_finite` → `hbox` → repoints `aoyagi_learning_coefficient`. The two live holes
are the ONLY engine-cone sorries besides the `canonicalResolution224` @[blueprint] forecast
(`CanonicalWitness224.lean:130`, expected). Census: [[dead-routes]] § fossil census (24 total tree-wide).

---

## R1 — construction carrier + faithful ledger + divisor-chooser (MEDIUM tide)

*Builds the resolution tree into `CanonicalResolution` — the structural half of
`monomialization_terminates`. Carrier + ledger + termination DONE; the chooser (full-`T`) is the
open fork-10 un-deferral.*

**Consumes (banked, sorry-free):**
- `minAdm` / `minAdmRec` / `minAdmRec_eq_minAdm` — `Validate/RouteMLayerSplit.lean:51,58,395`. The
  combinatorial budget; `decide`-computable. LIGHT (RouteMLayerSplit cone = 21).
- The μ-lex well-founded idiom `ℕ ×ₗ ℕ ×ₗ ℕ` + `InvImage.wf wellFounded_lt` — banked in
  `Validate/RouteMState.lean` (rung 2A surveyed it before building; no new WF machinery invented).
  Consumed by `conRel_wf` (`Engine/EngineConstruction.lean`, PROVED clean-three, tick 58). LIGHT (32).
- `Adm` / `admBound` / `Mval` — `Foundations/Lambda.lean:62,46,41`. The admissible cone (incl. the
  `j=1` block bound `min(M¹,M²)`, Def 3 p.8). LIGHT.

**Already built this expedition (do NOT rebuild — reuse in place):**
- `ResolutionTree` / `StepData` / `Edge` / `LeafData` (edge-labelled carrier) —
  `Engine/ResolutionTree.lean`. Import weight 4 (VERY LIGHT). r2-VALIDATED (tick 37).
- `RootLedger` + `stepUpdate` (3 cases, page-pinned) + faithful `StepRel := rootLedger e.child =
  stepUpdate n e.case e.subst` — in `Engine/EngineObligations.lean`. case-2 cleared advance is `+= 1`
  (p.21 truth-witness catch, tick 46 — NOT `+= resRows`). Eligibility conjunct `t̃(mergeIdx) =
  cleared + runLen` guards BOTH case-1 charts (tick 56).
- `ConState` / `StateInvariant` / per-case μ-descent (`conRel_stepCase11` /`_stepAppendAdvance`/
  `_stepRollover`, all clean-three, tick 59) — `Engine/EngineConstruction.lean`.

**Open (the chooser — fork-10 un-deferral, recon §4 fidelity delta).** The full `T`-vector carrier:
Aoyagi carries `T_{s,k}=(t¹,…,t^L)`; the engine stores only `t̃`. The p.15 minimality tie-break
(lex-min `T` per Def 4) and the J₁ gap condition NEED the full vector — both named
deliberately-uncaptured in the `StepRel` docstring, both the chooser's burden (elder tick 55).

---

## R2 — coverage / no-smaller-ratio: `ChartBridge` (HARD — the hardest named object)

*The one genuine new proof; landmark `coverage-theorem`. Lives INSIDE `monomialization_terminates`
(the bundle collapsed the fan-out — the covering CONTENT is in the construction hole, not its own
tide). Consumes the cover/null toolkit; may NOT consume `rlct=c*` (circularity guard).*

**Consumes (banked, sorry-free):**
- Finite box covers + measure-zero disposal — `Foundations/S1Cover.lean`, `S1BoxAdditive.lean`,
  `Validate/RouteMCoverLemmas.lean`, `Validate/RouteMNullSliceCov.lean`. LIGHT-MEDIUM. Load-bearing
  precondition: the SEPARATED leaf integrand (`IsFullMonomialization`), witnessed
  `g-leaf-chain-separation`, `g-pivot-conull`.
- The corank-2 coordinate-index model (`divCoord`/`resCoord` injective + disjoint over `Fin (flatDim
  M)`) — de-risked at (3,3,4) by `Engine/CoRank2Spike.lean` (rung 2C, tick 58; import weight 31).

**Gate (armed, do NOT skip):** the exhaustiveness hunt (`hunt-cert.md §5`) SURVIVED carrier-independent
(tick 12; 5 decorrelated legs, 0 undershoots) — no re-run needed, but a monomial-only hunt passes
vacuously; cite the scope by pointer, never "established". Kill = `g-coverage-sharing-killcond`.

---

## R3 — `region_glue` / per-leaf (HARD/MEDIUM — analytic hole)

*Per-leaf area-formula integration → box finiteness, glued over the finite subcover. The per-leaf
read MECHANISM CHANGED since pass #1 (elder tick 43): the banked local-homeomorph transport is
BANKED-BUT-UNUSED on this path; the read is now the Mathlib AREA FORMULA. See [[dead-routes]]
§ transport-on-leaf-path (retired-shape).*

**Consumes (banked, sorry-free):**
- **Area formula:** `lintegral_image_eq_lintegral_abs_det_fderiv_mul` +
  `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` (Mathlib, v4.29 — elder-verified
  present tick 43). Needs ONLY the UPPER det bound `|det Dφ| ≤ hi·∏|u|^{divExp−1}`.
- **Flat model read (the per-leaf target):** `model_read_lt_top` —
  `Validate/RegionGlueModelRead.lean:215` (NEW this expedition, Module A COMPLETE tick 60,
  clean-three). `∫_cube (∏|x|^e)(∑x²)^{−c'} < ⊤` for `e>−1`, `0<c'<nr/2`; a.e. AM-GM domination via
  `Measure.pi_hyperplane`. Import weight 27 (LIGHT).
- **Scaling bridge (globalization):** `lintegral_rpow_neg_smul_bridge` +`lintegral_smul_set` —
  `Foundations/S1ScalingBridge.lean:88,36` (NEW, tick 40, clean-three, Foundations-grade abstract
  `F`). LIGHT. NOTE: pass-#1 name `∫_{εK}F^{−c'}=ε^{N−2Lc'}∫_K` is `lintegral_rpow_neg_smul_bridge`.
- **DLN homogeneity (degree 2L):** `flatNodeLoss_smul` / `dlnLoss_zero_smul` /`prod_smul` —
  `Validate/D1L2ExplicitCoreProducer.lean`. **⚠ HEAVY (302-file cone).** RegionGlueGlobalize uses
  only the smul lemmas but drags the whole D1L2 explicit-core producer. RE-HOME candidate — see
  [[import-hygiene]] § D1L2 worked example. The smul lemmas themselves only need
  `Foundations/S1NodeFlatHomog.lean` + `Validate/LossHomogeneity.lean` + `ParamsFlatLinear`.
- **Haar on `Params M`:** `instIsAddHaarMeasureParams` / `instBorelSpaceParamsGlue` —
  `Engine/RegionGluePerLeaf.lean` (NEW, via `paramsEquivFlatCLE`; volume on `Params M` is NOT
  auto-Haar — transported from the flat cube). These two instances are ALL that's currently landed
  in RegionGluePerLeaf — the area-formula theorem itself is Module B, IN FLIGHT (task #2).

**Already built (globalization half, boundedness-independent):**
- `routeMLayerBoxIntegral_lt_top_of_small_box` + `cubeBox_smul` + `routeMLayerBoxIntegral_eq_flat` —
  `Engine/RegionGlueGlobalize.lean` (tick 45, clean-three). **⚠ HEAVY (304).** Namespace quirk: lives
  in `Engine/` but declares `namespace DLNFibre.DLN.RLCT` — see [[naming]].
- Interface is FROZEN (ChartBridge strengthened: MeasurableSet + bounded-in-flat-cube srcBox, tick
  46) and abstract-field-gate-CLEARED exactly-sufficient (tick 51 — no third conjunct needed).

**Open:** Module B (per-leaf area formula, `RegionGluePerLeaf`, task #2) → Module C (cover assembly +
globalize, task #3) → `leaf_chart_image_lintegral_lt_top` → `region_glue_of_chartBridge`.

---

## R4 — `genDivExp` support redesign (MEDIUM — fidelity)

*Multiplicity-valued `genDivExp : Fin numGen → Fin numDiv → ℕ`, restoring sharing-propagation
fidelity. NAMED rung (elder tick 46 condition on the R1 "middle path": support deliberately out of
rung 1, redesigned here). No banked substrate to consume — this is fresh fidelity work on the
carrier.*

**Guard / kill-condition (do NOT ship without):** `g-coupled-binding-334` (minAdm(3,3,4)=8 coupled
path only) + `g-delta-flatten` (identical multiplicities, different lct) re-checked. The current
binary `support : Fin numGen → Finset` is a nonzero-locus APPROXIMATION (recon §4); the exact
`LeafPullback` identity — not propagation — is what breaks coupling for the certificate, so R4 is
fidelity, not finiteness-load-bearing.

---

## R5 — wiring (MECHANICAL)

*Discharge `hbox`; repoint the canonical headline → `_gen`; delete `cited_aoyagi_dln`. The recon's
DECISIVE finding: this is a repoint + delete, NOT a build.*

**Consumes (banked, sorry-free — the whole consumer stack is PROVEN):**
- `aoyagi_learning_coefficient_gen` — `Validate/HeadlineGenAssembly.lean:55`. Clean-three, conditional
  SOLELY on `hbox = RouteMBoxThresholdFinite (H−r)` — uses NO `cited_aoyagi_dln`/`monomial_rlct`/
  `sorryAx` (recon §3, Lean-verified). **⚠ HEAVY (356-file cone = the value lane)** — unavoidable at
  wiring (the driver must SEE `_gen`); acceptable because R5 builds rarely. `EngineDriver` (359)
  inherits this.
- The `≤`-half (achiever divergence): `routeMCore_box_diverges_achiever_full'` —
  `Validate/RouteMAchieverFullHNoFree.lean:40`, 0-sorry. Folded with the finiteness half by
  `r1_resolution_general` (`Validate/R1ResolutionGeneral.lean`) into `= ofReal(lambdaCore M)`.
- Regular-peel / value-shift (Theorem 3): `reg_shift_add_core_eq_aoyagiLambda`
  (`Validate/DeepestFrontGaugeGen.lean` + consumers), `deepest_le_of_homogeneous_core`
  (`Validate/DeepestMinRlct.lean:157`, hypothesis-free — Theorem 4 deepest-point).
- `RouteMBoxThresholdFinite` (hbox predicate) — `Validate/RouteMBoxReduction.lean:165` (verbatim
  anchor). `engine_box_threshold_finite` (the discharger) — `Engine/EngineDriver.lean:44`
  (@[blueprint], sorry-free composition; its flip to clean-three IS the hbox event).
- MINT anchor: `aoyagi_learning_coefficient` bare name at `Skeleton.lean:1685` (legacy stub
  re-pointing at mint). ⚠ Skeleton.lean carries 3 legacy stub sorries (`:1094,:1140,:1197`) — see
  [[dead-routes]]; the repoint must land the bare name on `_gen`, not on a stub.

---

## R6 — regular-peel transcription (DISTINCT-BET, OPTIONAL, NOT critical-path)

*Lemma 2 + Theorem 3 (block-diagonalization) as first-class library objects, for full fork-10
fidelity. Recon §4 [Q]: the banked value lane already discharges Theorem 3's `[−r²+…]/2` shift, so
the recon RECOMMENDS the value lane suffices for λ; R6 first-class transcription is a distinct-bet.*

**Consumes (if adopted):** the value-lane peel is already banked (`reg_shift_add_core_eq_aoyagiLambda`,
`DeepestFrontGaugeGen`, `HeadlineRowColPermWLOG`, `D1Ge*` — all wired sorry-free in `_gen`). A
first-class transcription would build Lemma 2's Schur-complement CoV + Theorem 3's peel induction NOT
from these (they compute the value, not the objects). No banked object-level substrate — fresh work.

---

## Worked precedent (the pattern the generic engine reproduces)

`Validate/RouteMBoxThresholdRR4.lean` — the (r,r,4) family end-to-end 0-sorry. Assembly decl
`routeMBoxThresholdFinite_rr4_of_schurRecStep` (`:219`); threshold match `minAdm_rr4_eq` (`:88`);
CoV `routeMLayerBoxIntegral_rr4_eq` (`:177`). See [[landmark-cards]] `rr4-precedent`. **OUTER-plumbing
precedent ONLY** — the inner SchurCore/front-peel core walls at depth ≥ 3 (`:12–21`), so it does NOT
precedent the L=3 (2,2,2,2) case-1(1) merge (task #7). NOTE: shorthand "RR4.lean" = this file (no bare
`RR4.lean`).
