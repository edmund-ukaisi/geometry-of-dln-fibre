# Integration Reconnaissance — Aoyagi-Full Branch Map

**Date:** 2026-06-23  
**Base:** `expedition/aoyagi-full` (commit `6bc1b22c`)  
**Scope:** All branches with `fm2/*`, `fm3/*`, `crux2/*`, `fm/*`, `fm-2/*` activity in last ~24 h  
**Method:** git-only (no lake build). All claims git-verified via `git show`, `git diff`, `git merge-tree --write-tree`.

---

## 1. Branches Assessed

The following branches are live relative to `expedition/aoyagi-full`:

| Branch | Commits above base | Family |
|---|---|---|
| `fm3/routem` | ~55 | R1 dispatcher |
| `fm3/routem-ga-transport` | ~70 | R1 dispatcher + R1 lift |
| `crux2/r1-222-wrap` | ~56 | R1 (222-engine + schur close) |
| `fm2/split-reindex` | ~80 | L2 (split homeo, frame DATA) |
| `fm2/deepest-gauge-chart-sub34` | ~169 | L2 (deepestFrameFamily PROVEN) |
| `crux2/telescope-fold` | ~10 above sub34 common base | L2 (FOLD3 telescoping) |
| `crux2/fold3-close` | ~19 above telescope-fold base | L2 (FOLD3 + FOLD2 + shear CLE) |
| `fm/deriv-frame-resume-cont` | ~11 above sub34 | L2 (PIN1 regSlice fderiv + BoxThreshold) |
| `fm-2/consolidate-aoyagi-full` | 2 (ancestor of r1-222-wrap) | R1 (schur fix, subsumed) |

**Note on fm-2/consolidate:** Its 2 commits (hardPivot\_schur\_blockId + schur\_straighten\_of\_data) are already included in `crux2/r1-222-wrap`. It can be ignored for integration — no additional work to pick up.

---

## 2. Per-Branch Decl Ownership

### R1 family

**`fm3/routem`** (canonical R1 dispatcher, base of the R1 tree)
- Owns: `routeStep` dispatcher, `RouteMTree`, `case222_routeStep_branch`, `case222_routeStep_value`, `minAdm_M222`, `MinAdmMono` (sorry-free), `BindingArith`, `MvalMultSum` (376 lines, 0 sorries), all `RouteM*` scaffold files, `CascadeAchiever`, `CascadeRank`, `CascadeRealizable`, `LossContinuity`, geometric-codim bridge (#146 close: `MvalMultSum` collapse sorry).
- Lean files changed vs base (30 files): `CascadeAchiever.lean`, `CascadeRank.lean`, `CascadeRealizable.lean`, `LossContinuity.lean`, `Skeleton.lean`, `BindingArith.lean`, `CascadeAchiever.lean` (Validate), `Case222RouteMCover.lean`, `Case222RouteStep.lean`, `Case323RouteStep.lean`, `GeneralR1Recursion.lean`, `LossHomogeneity.lean`, `MinAdmMono.lean`, `MvalMultSum.lean` (full), `NodeHomogeneity.lean`, `ResolutionAtlas.lean`, `RouteMBranch.lean`, `RouteMBranchRead.lean`, `RouteMClassify.lean`, `RouteMCoverLemmas.lean`, `RouteMExtraction.lean`, `RouteMGeneralAssembly.lean`, `RouteMLeaf.lean`, `RouteMNReg.lean`, `RouteMRecursion.lean` (1 sorry), `RouteMScaffold.lean`, `RouteMState.lean`, `RouteMValue.lean`, `SchurNodeAssembly.lean`, `SchurState.lean`.
- `Skeleton.lean` sorries: 4 (L2, D1, R1, A2 — unchanged from base).
- `GeneralR1Recursion.lean` sorries: 1 (`schur_straighten_exists`).

**`fm3/routem-ga-transport`** (strictly ahead of `fm3/routem` on R1 lift; fm3/routem has 5 commits that routem-ga-transport lacks: the geometric-codim bridge + MinAdmMono wording)
- Adds on top of routem-ga-transport base: `S1BoxAdditive`, `S1BoxProductMin`, `S1BoxSqueeze`, `S1NodeBlowup`, `S1NodeCoverBridge`, `S1NodeCoverGE`, `S1NodeFlatHomog`, `S1WeightedProductMin` (ALL 0 sorries), `BindingRecursion` (0 sorries, PROVEN), `BindingSpine`, `Case222NodeDescent` (0 sorries), `RouteMNodeDescent` (0 sorries), `RouteMNodeDescentBuild`, `RouteMO1Bridge` (0 sorries), `RouteMAchieverForce`, `MvalMultSum` (shorter, 1 sorry — fm3/routem's version is better).
- `RouteMRecursion.lean` sorries: 3 (vs fm3/routem's 1).
- Does NOT have fm3/routem's geometric-codim bridge (#146 close) or MinAdmMono wording fix.
- `Skeleton.lean` sorries: 4 (unchanged).

**`crux2/r1-222-wrap`** (most advanced R1 branch overall; contains fm-2/consolidate + #94 milestone)
- Contains all of `fm3/routem`'s RouteM machinery (same file set, same ancestry path).
- Adds: `GeneralR1Recursion.lean` FULLY CLOSED (0 sorries) — `schur_straighten_exists` replaced by `schur_straighten_of_data` (sorry-free), `schur_straighten_squeeze_exists` PROVEN sorry-free, `rlctAtOn_reduced_transport` PROVEN, `schur_node_squeeze_unif` PROVEN.
- Adds: `RouteMRecursion.lean` 0 sorries (closed vs fm3/routem's 1).
- Adds: `ResolutionAtlas.lean` 0 code sorries (vs base's 1 in `GeneralR1Recursion`).
- Adds #94: `(2,2,2) RouteM cover → rlctAtOn = 3/2` milestone commit (sorry-free validation).
- `Skeleton.lean` sorries: 4 (unchanged, `resolution_charts` still sorry).
- **Bottom line for R1:** `crux2/r1-222-wrap` is the canonical R1 branch. It closes `schur_straighten_exists` and `RouteMRecursion` sorries. After merge, `GeneralR1Recursion.lean` and `RouteMRecursion.lean` are sorry-free. The `resolution_charts` sorry in Skeleton.lean remains (needs R1 value + atlas existence).

**Orphan work on `fm3/routem-ga-transport` not on any R1 branch:** The S1 lift foundations (8 axiom-clean files). These do not conflict with `crux2/r1-222-wrap` and should be merged separately.

### L2 family

**`fm2/split-reindex`** (earliest L2 branch; establishes the split homeo + frame as DATA)
- Owns: `RankNormalForm.lean`, `PolynomialZeroSet.lean`, `CoreShearMP.lean`, `DeepestSplitHaar.lean`, `S1NonMPTransport.lean`, `S1Spectator.lean`, `DeepestCoreNonvanishing.lean`, `DeepestFrame.lean` (147 lines), `DeepestGaugeChart.lean` (591 lines, 2 sorries in `deepest_gauge_squeeze_exists` + `deepest_regular_core_normal_form`), `DeepestMinRlct.lean`, `DeepestNormalFormWiring.lean` (3 sorries), `DeepestSplitReindex.lean`, `GeneralR1Recursion.lean` (1 sorry, older version), `ResolutionAtlas.lean` (3 sorries).
- Adds `deepest_regular_core_normal_form` named sorry to Skeleton.lean (+1 sorry, total 4 in Skeleton but the L2 gate is now explicitly named).
- `Skeleton.lean` sorries: 4.

**`fm2/deepest-gauge-chart-sub34`** (L2 branch with deepestFrameFamily PROVEN; diverged from split-reindex, 158 commits ahead, 11 behind)
- Adds on top of split-reindex base: `deepestFrameFamily_exists` PROVEN (sorry-free), `prod_deepestPoint_eq` PROVEN, `DeepestFramedProduct.lean` (379 lines, 0 sorries), `DeepestGaugeBlocks.lean` (614 lines, 0 sorries), `DeepestGaugeConstruction.lean` (907 lines, 2 code sorries at lines 456, 632), `DeepestGaugeDiffeo.lean` (89 lines, 0 sorries), `DeepestNormalFormWiring.lean` (3 sorries), `DeepestTelescoping.lean` (independent version, 0 code sorries).
- `DeepestFrame.lean`: 352 lines, 0 sorries (vs split-reindex's 147). More advanced.
- Does NOT have split-reindex's unique commits: `deepestPoint_frame + _normal + _invertible` DATA exposure, `regStraighten dE(0)=id` correction, `deepestEPivot _deriv` correction.
- Conflicts with `crux2/telescope-fold` and `crux2/fold3-close` on `DeepestTelescoping.lean` (add/add conflict: both independently created this file).

**`crux2/telescope-fold`** (FOLD3 telescoping; strictly ahead of crux2's sub34 common base)
- `DeepestTelescoping.lean`: 253 lines, 2 code sorries (`endpoint_telescoping` open).
- `DeepestGaugeConstruction.lean`: 3 code sorries (vs sub34's 2).
- `DeepestGaugeChart.lean`: 1 code sorry.

**`crux2/fold3-close`** (most advanced L2 branch for the telescope/FOLD work; 19 commits ahead of telescope-fold)
- `DeepestTelescoping.lean`: 362 lines, **0 code sorries** (endpoint_telescoping PROVEN via FOLD3).
- `DeepestGaugeConstruction.lean`: 2 code sorries (better than telescope-fold's 3).
- `DeepestGaugeChart.lean`: 1 code sorry (`deepest_gauge_squeeze_exists`).
- Also adds: `reindex_mul_distrib_left/right` kernels, `regStraightenTotalCLM_equiv_of_regBlock_id` (shear CLE, Route D), `hasStrictFDerivAt_prodAux_entry` (product-derivative machine), `FOLD2` assembly structure.

**`fm/deriv-frame-resume-cont`** (PIN1 + BoxThreshold; strictly ahead of sub34 by ~11 commits)
- Adds: `BoxThresholdBridge.lean` (207 lines, 0 sorries) — the box→point RLCT collapse, `DeepestRegSliceFderiv.lean` (560 lines, 0 code sorries per tactic-grep), `DeepestSchurShift.lean` (455 lines, 0 sorries), `DeepestRegAbsorbIFT.lean` (547 lines, 0 sorries).
- `DeepestGaugeConstruction.lean`: 2 code sorries (same count as fold3-close, different content).
- Merges cleanly with `fm2/deepest-gauge-chart-sub34` (0 conflicts).
- Conflicts with `crux2/fold3-close` on `DeepestTelescoping.lean`.

---

## 3. Conflict Map

The `git merge-tree --write-tree` test results (non-zero exit = conflict):

```
CONFLICT PAIRS:
  fm3/routem              + fm3/routem-ga-transport  => MvalMultSum.lean (add/add)
  fm2/split-reindex       + fm2/deepest-gauge-chart-sub34 => DeepestFrame.lean (content)
  fm2/deepest-gauge-chart-sub34 + crux2/telescope-fold  => DeepestTelescoping.lean (add/add)
  fm2/deepest-gauge-chart-sub34 + crux2/fold3-close    => DeepestTelescoping.lean (content)
  crux2/telescope-fold    + crux2/fold3-close          => DeepestTelescoping.lean (add/add)
  crux2/telescope-fold    + fm/deriv-frame-resume-cont => DeepestTelescoping.lean (add/add)
  crux2/fold3-close       + fm/deriv-frame-resume-cont => DeepestTelescoping.lean (content)

CLEAN PAIRS (all others including):
  fm3/routem-ga-transport + fm2/split-reindex       OK
  fm3/routem-ga-transport + fm2/deepest-gauge-chart-sub34 OK
  crux2/r1-222-wrap       + fm2/split-reindex       OK
  crux2/r1-222-wrap       + fm2/deepest-gauge-chart-sub34 OK
  crux2/r1-222-wrap       + fm3/routem-ga-transport  OK
  crux2/fold3-close       + fm3/routem              OK
  crux2/fold3-close       + fm3/routem-ga-transport  OK
  fm/deriv-frame-resume-cont + crux2/r1-222-wrap    OK
  fm/deriv-frame-resume-cont + fm3/routem           OK
  fm2/split-reindex       + crux2/telescope-fold    OK
  fm2/split-reindex       + crux2/fold3-close       OK
  fm2/split-reindex       + fm/deriv-frame-resume-cont OK
  fm2/deepest-gauge-chart-sub34 + fm/deriv-frame-resume-cont OK
```

**Conflict resolution rules (all three conflicts resolve the same way):**
- `MvalMultSum.lean`: take `fm3/routem`'s version (376 lines, 0 sorries) over routem-ga-transport's (60 lines, 1 sorry).
- `DeepestFrame.lean`: take `fm2/deepest-gauge-chart-sub34`'s version (352 lines, 0 sorries) over split-reindex's (147 lines, 0 sorries) — sub34 is the more developed version.
- `DeepestTelescoping.lean` (all three occurrences): take `crux2/fold3-close`'s version (362 lines, **0 sorries**) — endpoint_telescoping is PROVEN there.

---

## 4. Canonical Branch Per Gate

| Gate | Best Branch | Key Decls | Skeleton Sorry | Supporting Module State |
|---|---|---|---|---|
| **L2** `product_reduction` | `crux2/fold3-close` (then `fm/deriv-frame-resume-cont`) | `deepest_regular_core_normal_form` | still sorry | `DeepestGaugeConstruction`: 2 code sorries; `DeepestTelescoping`: 0 sorries (endpoint_telescoping PROVEN); `DeepestGaugeChart`: 1 sorry (`deepest_gauge_squeeze_exists`) |
| **D1** `rlctAt_deepest_le_of_optimal` | any (no branch has closed it) | same Morse-split machinery as L2 | still sorry | blocked on the same gauge-chart machinery as L2 |
| **R1** `resolution_charts` | `crux2/r1-222-wrap` | `schur_straighten_squeeze_exists` (PROVEN), `RouteMRecursion` (0 sorries), `GeneralR1Recursion` (0 sorries) | still sorry | `resolution_charts` itself remains sorry; the supporting recursion engine is now sorry-free |
| **A2** `aoyagiTheta_eq` | none (all branches sorry) | — | still sorry | Not worked on any active branch |
| **L2 PINs / DeepestGaugeChart** | `fm/deriv-frame-resume-cont` (PIN1 regSlice fderiv + BoxThreshold) + `fm2/deepest-gauge-chart-sub34` (deepestFrameFamily PROVEN) | `BoxThresholdBridge` (0 sorries), `DeepestRegSliceFderiv`, `DeepestRegAbsorbIFT`, `DeepestSchurShift` (all 0 sorries), `deepestFrameFamily_exists` (PROVEN) | — | `DeepestGaugeConstruction` 2 sorries remain |
| **R1 routeStep dispatcher** | `fm3/routem` (for MvalMultSum + codim bridge) combined with `crux2/r1-222-wrap` | `routeStep`, `RouteMTree`, `MinAdmMono`, `case222_routeStep_value` (0 sorries) | — | All RouteM validation files sorry-free after r1-222-wrap merge |

---

## 5. Recommended Integration Order

The goal is zero-conflict sequential merges where possible, with the fewest manual resolutions.

**Serialization rule:** branches that conflict on a file must be serialized (one merged first, then the other applied on top). From the conflict map above, the two conflict clusters are:
- Cluster A (R1/MvalMultSum): `fm3/routem` vs `fm3/routem-ga-transport` — serialize.
- Cluster B (DeepestTelescoping/DeepestFrame): any branch that has touched DeepestTelescoping must be serialized — specifically `crux2/fold3-close` must come BEFORE `fm/deriv-frame-resume-cont` and before `fm2/deepest-gauge-chart-sub34`.

**Recommended order:**

```
Step 1: git merge origin/crux2/r1-222-wrap
        (clean merge into aoyagi-full; closes schur sorries, RouteMRecursion, GeneralR1Recursion)

Step 2: git merge origin/fm3/routem-ga-transport
        MANUAL CONFLICT on MvalMultSum.lean: take fm3/routem's version (376-line, 0-sorry)
        (adds 8 sorry-free S1 foundation files + BindingRecursion PROVEN + RouteMNodeDescent 0-sorry)
        Note: also accept routem-ga-transport's version of RouteMRecursion (it will conflict with
        r1-222-wrap if both touch same file — check if RouteMRecursion is identical first)

Step 2b: git merge origin/fm3/routem  
        (picks up geometric-codim bridge #146 close + MinAdmMono wording + MvalMultSum full version)
        May be clean after step 2 if step 2 resolved MvalMultSum. Alternatively merge before step 2.

Step 3: git merge origin/crux2/fold3-close
        (clean merge relative to r1-222-wrap and routem; closes DeepestTelescoping endpoint_telescoping;
         closes one DeepestGaugeConstruction sorry)

Step 4: git merge origin/fm/deriv-frame-resume-cont
        MANUAL CONFLICT on DeepestTelescoping.lean: take crux2/fold3-close's version (already merged).
        (adds BoxThresholdBridge 0-sorry, DeepestRegSliceFderiv, DeepestRegAbsorbIFT, DeepestSchurShift)

Step 5: git merge origin/fm2/deepest-gauge-chart-sub34
        MANUAL CONFLICT on DeepestTelescoping.lean: take already-merged (fold3-close) version.
        MANUAL CONFLICT on DeepestFrame.lean: take sub34's version (352-line, 0-sorry).
        (adds deepestFrameFamily_exists PROVEN, DeepestGaugeBlocks 0-sorry, DeepestGaugeConstruction)
```

**Alternative (fewer conflicts) if Steps 4+5 are merged as a unit first:**
Since `fm/deriv-frame-resume-cont` and `fm2/deepest-gauge-chart-sub34` merge CLEANLY together (verified), the controller could:
- Create a scratch branch: merge sub34 into deriv-frame (or vice versa) — no conflicts.
- Then merge that combined branch into expedition/aoyagi-full after step 3.
- DeepestTelescoping conflict happens once (take fold3-close's version).

**Steps 2/2b ordering clarification:** `fm3/routem` and `fm3/routem-ga-transport` conflict only on `MvalMultSum.lean`. If `fm3/routem` is merged first, then routem-ga-transport can be applied with the MvalMultSum conflict resolved by keeping what's already there (the 376-line version). So: **merge `fm3/routem` before `fm3/routem-ga-transport`.**

---

## 6. Expected Sorry Count After Full Integration

After all merges (with conflicts resolved per the rules above):

**In Skeleton.lean:** 4 tactic sorries remain (L2, D1, R1, A2 — unchanged).

**In supporting modules (code-level sorry instances):**

| File | Before | After |
|---|---|---|
| `GeneralR1Recursion.lean` | 1 | **0** (closed by crux2/r1-222-wrap) |
| `RouteMRecursion.lean` | 1 (fm3/routem) | **0** (closed by crux2/r1-222-wrap) |
| `DeepestTelescoping.lean` | (new file) | **0** (endpoint_telescoping PROVEN by crux2/fold3-close) |
| `DeepestGaugeConstruction.lean` | (new file) | **2** (still open: the two sub-lemmas inside the Morse normal-form) |
| `DeepestGaugeChart.lean` | (new file) | **1** (deepest_gauge_squeeze_exists, the heavy IFT obligation) |
| `DeepestNormalFormWiring.lean` | (new file) | **3** |
| `ResolutionAtlas.lean` | 3 (fm2 path) | **0** (crux2/r1-222-wrap path has 0 code sorries) |
| `DeepestRegSliceFderiv.lean` | (new file) | **0** (fm/deriv-frame-resume-cont, PIN1 work) |
| `BoxThresholdBridge.lean` | (new file) | **0** |
| `DeepestRegAbsorbIFT.lean`, `DeepestSchurShift.lean` | (new) | **0** each |
| S1 foundation files (8 files) | (new) | **0** each |

**Headline gates after merge:**
- L2 `product_reduction`: still sorry (gated on `deepest_regular_core_normal_form`, which needs `deepest_gauge_squeeze_exists` = the IFT wall; 1 sorry in DeepestGaugeChart).
- D1 `rlctAt_deepest_le_of_optimal`: still sorry (same dependency on gauge-chart machinery).
- R1 `resolution_charts`: still sorry (the atlas existence itself; the supporting recursion is now sorry-free, which substantially de-risks R1).
- A2 `aoyagiTheta_eq`: still sorry (untouched on any branch).

**The headline `aoyagi_learning_coefficient` remains conditional on all 4.**

---

## 7. Single-Writer Overlap Summary

Files that appear in multiple conflicting branches (serialization required for these):

| File | Branches touching it | Winner |
|---|---|---|
| `DeepestTelescoping.lean` | sub34, telescope-fold, fold3-close, deriv-frame-resume-cont | `crux2/fold3-close` (0 sorries, PROVEN) |
| `DeepestFrame.lean` | split-reindex, sub34 | `fm2/deepest-gauge-chart-sub34` (352 lines, 0 sorries) |
| `MvalMultSum.lean` | fm3/routem, fm3/routem-ga-transport | `fm3/routem` (376 lines, 0 sorries) |
| `Skeleton.lean` | all branches | All add disjoint content — auto-merges clean (verified) |
| `GeneralR1Recursion.lean` | aoyagi-full, fm3/routem, crux2/r1-222-wrap, fm-2/consolidate | `crux2/r1-222-wrap` (0 sorries) |

Files with no cross-branch conflicts (all auto-merge clean):
- All 8 S1 foundation files (unique to routem-ga-transport).
- `BoxThresholdBridge.lean`, `DeepestRegSliceFderiv.lean`, `DeepestSchurShift.lean`, `DeepestRegAbsorbIFT.lean` (unique to fm/deriv-frame-resume-cont).
- `DeepestFramedProduct.lean`, `DeepestGaugeBlocks.lean`, `DeepestGaugeDiffeo.lean` (unique to sub34/fold3-close family).
- All RouteM* files (unique to fm3/routem lineage, no cross-family conflicts).

---

## 8. Branches to Skip / Archive

- `fm-2/consolidate-aoyagi-full`: subsumed by `crux2/r1-222-wrap`. Skip.
- `crux2/telescope-fold`: subsumed by `crux2/fold3-close` (fold3-close is strictly ahead and has 0 DeepestTelescoping sorries). Skip, take fold3-close instead.
- `fm2/split-reindex`: subsumed by `fm2/deepest-gauge-chart-sub34` for all content except the unique commits re: `deepestEPivot _deriv` correction and `deepestPoint_frame` DATA exposure. The controller should check whether those unique split-reindex commits (11 commits: `deepestEPivot_sq_sum_eq_blocks`, `slot-index map cert`, `ReducedTransport bundle`, etc.) are already reflected in sub34 or are genuinely missing. If missing and needed, cherry-pick those 11 commits onto sub34 before step 5; otherwise skip split-reindex.

---

_Reconnaissance by scout agent, 2026-06-23. All sorry counts are tactic-level (`  sorry` lines), not doc-comment mentions. Branch mergeability is git-verified (exit code 0 from `git merge-tree --write-tree`). No lake build performed._
