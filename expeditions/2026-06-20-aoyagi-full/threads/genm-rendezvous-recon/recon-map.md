# RENDEZVOUS recon-map — the (□) final-integration spec (VERIFIED against live branch state)

**Thread `genm-rendezvous-recon` (self-recon, read-only). 2026-07-14.** Every branch tip, file version,
signature, and sorry-status below is verified against the ACTUAL git objects (`git show <hash>:<path>`),
NOT the ledger summary. Discrepancies vs the ledger are flagged ⚠. Base for the rendezvous = **canonical
`expedition/aoyagi-full` @a87c0506** (file-level assembly, the asmbase pattern).

---

## 0. HEADLINE — what to reuse, what's staged, what still needs a hand at rendezvous

The two isolated builds ARE done and sorry-free **in their key results** (crux `pivotPeel_domination` +
`forward_LHS_finiteness` in PivotFin; O2 `routeMLayerBoxIntegral_comp_rev` + `routeMBoxThresholdFinite_of_rev`
in WaistReversalCoV). The rendezvous is a **file-level assembly off canonical** — NOT a naive `git merge`
(that would add/add-conflict the 3 crux files). BUT it is **not "mechanical wiring"**: there are five
genuine (bounded) fills/decisions the controller owns, listed here so none is a surprise on mint day.

**★ Two load-bearing surprises the ledger's "crux SORRY-FREE" headline hides:**
1. ⚠ **`genm-sj5-step2` local ref is STALE (@e60260db).** The crux SORRY-FREE work (e395121c) is on
   **`origin/genm-sj5-step2`** and in the locked worktree `agent-a1b4ad8d7e1c75556`. Same for waist:
   local `genm-sj5-waist`=@62fa2592 stale; the O2 work (cf47a1a9) is on **`origin/genm-sj5-waist`**.
   **`git fetch origin` FIRST** and integrate from the `origin/*` tips (they match the task's cited hashes exactly).
2. ⚠ **"Crux SORRY-FREE" = PivotFin only.** `RouteMSJPivotDom` (3 sorries) and `RouteMSJHeadSplitDom`
   (2 sorries) on step2 are NOT sorry-free — they are the **thin stubs verbatim-wired to PivotFin at
   rendezvous** (their `_impl` twins in PivotFin are the filled versions). This is designed, but it means
   the controller must do the stub→impl wiring (mostly one-line `exact`s) + fill one real plumbing sorry
   (`shellSpine_le_hsQ_box`, shell-restricted) + moot/delete `pivotDom_uzero`.

**Confirmed-clean, consume as-is:** PivotFin crux (0 sorries), WaistConnector `deeperFlagWaist_finite_impl`
(0), WaistReversalCoV O2 (0), GoodConnector `deeperFlagGood_finite_impl` (0 body, hyp-parameterised),
DecoratedStep `decoratedStepHyp_dispatch` (0) + hole (e) `deeperFlagWaistM1_finite` (0), DeeperFlagCore
`exists_headSplitFrame`/`deeperFlag_spineToCore`/`deeperFlag_shell_le` (0 body; one D-assembly stub open),
mint `_prestage`/`_L1` (0). No cross-file name clashes (128 decls, 0 dups).

**The 5 genuine rendezvous tasks (all bounded):**
- (T1) Wire step2's PivotDom/HeadSplitDom stubs → their PivotFin `_impl` twins (mostly verbatim `exact`).
- (T2) Fill `shellSpine_le_hsQ_box` (shell-restricted) — the non-shell filled proof is on **assembly**; adapt it.
- (T3) Decide + execute the **frame-strip vs frame-supply** for brick D (the vestigial hcvg/U_sf/hfloor apparatus).
- (T4) Extract O1 `decoratedBoxThresholdFinite_of_routeMBoxThresholdFinite` from GoodConnector; supply to (c)+(d).
- (T5) Resolve the **import-topology** for the dispatch (WaistConnector imports DecoratedStep) — re-home OR refactor.

---

## 1. BRANCH TIPS + CONTRIBUTIONS (verified `origin` = ledger; locals partly stale)

| Branch | `origin` tip (= task's hash) | local tip | Owns (authoritative files) | in-file real sorries |
|---|---|---|---|---|
| genm-sj5-step2 | **e395121c** | ⚠ e60260db (STALE) | `RouteMSJPivotFin` (1333 L, crux), `RouteMSJPivotDom` (162 L, stubs), `RouteMSJHeadSplitDom` (287 L, D-assembly) | PivotFin **0**; PivotDom **3** (@89/103/115); HeadSplitDom **2** (@108/234) |
| genm-sj5-waist | **cf47a1a9** | ⚠ 62fa2592 (STALE) | `RouteMSJWaistConnector` (c), `RouteMSJWaistReversalCoV` (O2) [+3 SUPERSEDED orphans] | Connector **0**; ReversalCoV **0**; (WaistCharge/SchurChart/SchurChartGen **4/3/3 — orphans, DROP**) |
| genm-sj5-good | 8672869f | 8672869f | `RouteMSJGoodConnector` (d) — **O1 SOURCE** | GoodConnector **0** (body; `hstrict/hsat/hsector/hred`-parameterised) |
| genm-sj5-brickF-wire | 759fcf72 | 759fcf72 | `RouteMSJDeeperFlagCore` (F wired) + AxCheck | DeeperFlagCore **1** (@549 = `headSplit_domination` D-stub) |
| genm-sj5-holesbe | 4068d740 | 4068d740 | `RouteMSJDecoratedStep` (dispatch + holes a/b/c/d stubs + **e filled**) | 4 stub sorries (a@269,b@303,d@325,c@351); dispatch + (e) **0** |
| genm-sj5-assembly | ea55126a | ea55126a | base reconcile of the 4 shared files; **has FILLED non-shell `shellSpine_le_hsQ_box`** | (stub versions; superseded by step2 for 3 files) |
| genm-sj5-mintrehearsal | 2dc2682a | 2dc2682a | `HeadlineL1Mint`(re-home), `Skeleton`(→_legacy), `RRR`, `MintRehearsal108`, AxCheck | HeadlineL1Mint **1** (@106 = the (□) hole); MintRehearsal108 **1** |

**Sorry-classification method:** raw `grep sorry` over-counts (docstrings say "sorry-free"/"sorried"); the
counts above are actual `sorry` *terms* (filtered comments). **#print-axioms footprints NOT independently
re-run** (a force-recompile of the crux import closure is hours; out of scope for read-only recon). The
ledger reports forced clean-three on `pivotPeel_domination`+`forward_LHS_finiteness` @9f069059 (canonical
commit) and O2 pending. In-file sorry-freeness (above) is the cheap ground-truth I DID verify; recommend
the controller run forced `#print axioms` at the final gate on: `pivotPeel_domination`, `forward_LHS_finiteness`,
`routeMLayerBoxIntegral_comp_rev`, and the minted `aoyagi_learning_coefficient` (stale-olean lesson §7).

---

## 2. MERGE ORDER + CONFLICT RISKS

**Do NOT `git merge` the branches.** Canonical @a87c0506 lacks `RouteMSJ{HeadSplitDom,PivotDom,PivotFin,
DecoratedStep}` entirely (they are assembly-line files; canonical's Lean tree == fixed-adm @80932d88 —
every commit since is pure `docs(genm-inj)`). step2 branched at **28d75e7f** (pre the fixed-adm reconcile),
so its 3 crux files are a SEPARATE lineage from assembly's; good/waist/holesbe carry assembly's *stub*
versions of the same 3 files unchanged. A branch-merge therefore add/add-conflicts every shared file.

**Use file-level assembly (asmbase pattern).** rendezvous = canonical, then for each file take the ONE
authoritative source:

| File | Take from | Note |
|---|---|---|
| `RouteMSJPivotFin.lean` | **step2 e395121c** | 1333 L, crux filled (PivotFin authoritative; assembly's 325 L is a stale stub) |
| `RouteMSJPivotDom.lean` | **step2 e395121c** | 162 L thin stubs → wire to PivotFin (T1) |
| `RouteMSJHeadSplitDom.lean` | **step2 e395121c** | 287 L, shell-restricted, `pivotShell` def, hc0-threaded (assembly's 488 L is pre-shell) |
| `RouteMSJDecoratedStep.lean` | **holesbe 4068d740** | 563 L (= assembly 335 + (b)/(e) fills); dispatch here |
| `RouteMSJGoodConnector.lean` | good 8672869f | new file |
| `RouteMSJWaistConnector.lean` | waist cf47a1a9 | new file |
| `RouteMSJWaistReversalCoV.lean` | waist cf47a1a9 | new file (O2) |
| `RouteMSJDeeperFlagCore.lean` | brickF 759fcf72 | F wired; one D-stub open |
| `Skeleton.lean`, `RRR.lean`, `HeadlineL1Mint.lean` | mint 2dc2682a | re-home; true-mint deletes `_legacy` |
| `AxCheck.lean` | **controller-authored** | harvest audit entries from brickF + mint (single-writer) |

**Name clashes: NONE.** All 128 new/authoritative top-level decls are distinct across files. Each new name
was green against canonical on its own branch, so no clash with pre-existing canonical names either.

**Files edited on multiple branches (real overlap):**
- The 3 crux files (`HeadSplitDom`/`PivotDom`/`PivotFin`) — resolved by "take step2" (above); good/waist/
  holesbe's copies are just the assembly stub baseline, discard them.
- `RouteMSJDecoratedStep` — assembly (335, dispatch skeleton), holesbe (563, +b/e). **Take holesbe.**
- `AxCheck.lean` — brickF (+7 L, exists_headSplitFrame audit) AND mint (+14 L, re-home audit). Not a
  genuine conflict: AxCheck is controller-authored at the final gate; **harvest both audit entries.**

**⚠ DROP the 3 superseded waist orphans** (`RouteMSJWaistCharge`, `…WaistSchurChart`, `…WaistSchurChartGen`,
carrying 4/3/3 sorries). WaistConnector does NOT import them; if wired into `DLNFibre.lean` they break the
sorry-gate. They are the retired SVD-qPeel route — do not include.

---

## 3. STUB SIGNATURES TO THREAD (T1, T3 + `0≤c'` + `u≥1`)

### 3a. PivotDom stubs → PivotFin `_impl` twins (T1, mostly one-line)
step2's `RouteMSJPivotDom` (162 L) declares stubs whose FILLED verbatim twins live in `RouteMSJPivotFin`:

| PivotDom stub (sorry) | PivotFin filled twin | Wiring |
|---|---|---|
| `pivotDom_finiteness` @89 (frame sig: hcvg/U_sf/hrank/hfloor) | `pivotDom_finiteness_impl` (docstring: "Verbatim statement … controller wires the stub to it") | one-line `exact pivotDom_finiteness_impl …` |
| `pivotDom_RHS_ne_zero` @103 (sig lacks `hc0`) | `pivotDomRHS_ne_zero_aux` (sig HAS `hc0`) | ⚠ thread `hc0` (source below) — not verbatim |
| `pivotDom_uzero` @115 (`LHS ≤ RHS`) | — (PivotFin has `pivotDom_finiteness_uzero : LHS<⊤`, different shape) | **moot via u≥1 + DELETE** (below) |

Once the 3 are closed, `headSplit_pivotDom_impl` (@122, body already sorry-free) is fully sorry-free.

### 3b. HeadSplitDom stubs (2 sorries)
- `headSplit_pivotDom` @85 (sorry @108) — verbatim conclusion of `PivotDom.headSplit_pivotDom_impl`;
  one-line `exact` after 3a closes.
- ⚠ `shellSpine_le_hsQ_box` @210 (sorry @234) — **a GENUINE fill, not a wire (T2).** Its shell-restricted
  form (`… ∩ pivotShell M u ε Zf z`) was re-opened by step2's shell-ripple. **The NON-shell filled proof
  is on `assembly` (ea55126a): `shellSpine_le_hsQ_box` there is sorry-free** (assembly's only HeadSplitDom
  sorry is the crux stub @92). Adapt assembly's proof to the shell-restricted domain ("drop the shell
  indicator, ≥0" per the docstring). The plumbing branch `genm-sj5-headsplit-dom` @693bf5a5 is the origin
  of assembly's fill (also adds `measurable_hsQ_freedLoss_integral`, which step2 lacks — pull it if needed).
  Bounded, pure measure-reorganisation; NOT one-line.
- `headSplit_domination_impl` @238 — body sorry-free; calls the two above.

### 3c. `0 ≤ c'` threading — SOURCE CONFIRMED
step2 already added `(hc0 : 0 ≤ c')` to `pivotPeel_domination`/`forward_LHS_finiteness`/`headSplit_pivotDom(_impl)`.
The DeeperFlagCore→DecoratedStep chain sources `0<c'` (hence `0≤c'`) from **`deeperFlag_shell_le`'s
`(hc' : ((M0−t−j)·(M1−t−j))/2 < c')`** (= `ab/2 < c'`) and DecoratedStep (a)/(b)'s identical `hc'`: since
`ab/2 ≥ 0`, `hc'` gives `0 < c'`. Verified present on both stubs.

### 3d. `u ≥ 1` and MOOTING `pivotDom_uzero` — CONFIRMED mootable, but must DELETE
- **u≥1 holds throughout the head-split:** `u = t+j`, and the shell chain carries `ht1 : 1 ≤ t`
  (present on `deeperFlagStrictShell_finite`, `deeperFlag_shell_le`, `shellSpine_le_hsQ_box`,
  `headSplit_domination_impl`). So `u = t+j ≥ t ≥ 1`. `pivotPeel_domination` requires `hu : 1 ≤ u`; this is
  discharged by `Nat.le_add_right`+`ht1` at the call site. Confirmed sound.
- ⚠ **`pivotDom_uzero` is only reached in `headSplit_pivotDom_impl`'s `u=0` branch** (`rcases Nat.eq_zero_or_pos u`).
  To moot: add `(hu : 1 ≤ u)` to `headSplit_pivotDom_impl` and DELETE the `u=0` branch (thread `hu` from
  `headSplit_domination_impl`'s `ht1`). **Then `pivotDom_uzero` becomes unreferenced — it must be DELETED**
  (a sorried-but-unused theorem still fails the file's sorry-gate). Alternative: fill it (`decLoss=0 ⟹
  LHS≤RHS`, ~100 L, decLoss trivially 0 at u=0). Deletion is cleaner. Small signature ripple: `hu` added to
  `headSplit_pivotDom(_impl)`, discharged at the one call site in `headSplit_domination_impl`.

### 3e. ⚠⚠ THE BIG DESIGN DECISION — vestigial frame (T3)
`pivotPeel_domination`'s body uses ONLY `{hu, hε, c', hc0, hnd, hpiv, Zf, hZfMeas}` (verified: it calls
`pivotDomRHS_ne_zero_aux` / `pivotDomRHS_eq_top_of_critical` / `minAdm_add_peel_le` / `pivotDomLHS_lt_top_of_pos`
/ `pivotDomLHS_lt_top_of_zero` — none touch the frame). **The entire frame apparatus `{m, hcvg, hmM, ε',
hε', U_sf, hUs, hrank, hfloor}` is VESTIGIAL** — carried by every crux signature but never used. This
confirms cruxfin's "hcvg-free full-block" claim at the code level.

The controller must choose, and it is the single biggest rendezvous decision:
- **Option (a) SUPPLY the frame** (the original brick-D plan): construct `U_sf` (orthonormal, from Brick F's
  `measurableEigendecomp`) + `hfloor` (Ky-Fan, D-C `shell_subset_goodSet`) in `deeperFlag_spineToCore`.
  Preserves step2's files untouched. But it re-introduces the (now-unnecessary) frame construction the
  simplification was meant to kill. NOTE `U_sf=0` is NOT a valid trivial witness (`hUs : U_sfᵀU_sf = 1`
  forbids it), so the frame cannot be dummy-discharged — option (a) is real work.
- **Option (b) STRIP the frame** from `pivotPeel_domination`/`forward_LHS_finiteness`/`headSplit_pivotDom`/
  `pivotDom_finiteness(_impl)`/`headSplit_domination_impl` (delete `{m,hcvg,U_sf,hUs,hrank,hfloor,…}`).
  Bodies already ignore them, so bodies stay green; then `deeperFlag_spineToCore` needs no frame at all.
  Cleaner and matches "the frame apparatus is dead", but touches step2's authoritative files.

  **Recommendation: option (b)** (matches the hcvg-drop the ledger already committed to: "controller
  re-architects deeperFlag_spineToCore/shell_le … drop vestigial hconv/frame"). Worth a decorrelated Codex
  sanity pass before editing the crux files. Either way, the DeeperFlagCore `headSplit_domination` stub
  (@513, canonical) still carries the frame and LACKS `hc0/hjr/hε'le/hGmeas` that step2's `_impl` adds — the
  stub signature must be reconciled to `headSplit_domination_impl` and the extras discharged in
  `deeperFlag_spineToCore` (planned in the endgame ledger, item "DeeperFlagCore stub refinements").

---

## 4. O1 EXTRACTION (T4)

**O1 = `decoratedBoxThresholdFinite_of_routeMBoxThresholdFinite`**, consumed by (c) as the hypothesis
`hred` on `WaistConnector.deeperFlagWaist_finite_impl` (verified exact shape):
```
hred : ∀ {K} (M' : Fin (K+1+1+1) → ℕ) (D' : SJDecoration M'),
         adm (K+1+1) M' D' → RouteMBoxThresholdFinite M' → DecoratedBoxThresholdFinite D'
```
**Source = `GoodConnector.deeperFlagGood_finite_impl` (good @331).** Its proof, after the `M 1 = 0`
degenerate guard, does `suffices hbox : routeMLayerBoxIntegral M (c':ℝ) 1 < ⊤ by …` — and that `by`-block
IS the O1 content: the d=0/d≥1 `FaithfulSJAt` dispatch + `a_eq_M0_of_domEq` (the load-bearing volume
linchpin, filled clean-three) + the Tonelli monomial-separation reducing `D.integral` to the box integral.
**Minimal extraction:** factor that block into a standalone lemma taking `(M) (D) (hD) (hnd)` and the box
finiteness, concluding `DecoratedBoxThresholdFinite D`. Then:
- (d) `deeperFlagGood_finite_impl` calls O1 with `hbox` from its cover (`routeMBox_le_shellSum` + a/b/sector).
- (c) `deeperFlagWaist_finite_impl` receives O1 as `hred` and supplies `RouteMBoxThresholdFinite M` (via
  `routeMBoxThresholdFinite_mnp` at L=0 / reversal at L≥1).

⚠ **Shape reconciliation:** GoodConnector's `suffices` is phrased `routeMLayerBoxIntegral M c' 1 < ⊤`,
but O1/`hred` takes `RouteMBoxThresholdFinite M'` (a `Prop`, `RouteMBoxReduction:165`). Confirm
`RouteMBoxThresholdFinite M` unfolds to `∀ c' < threshold, routeMLayerBoxIntegral M c' 1 < ⊤` so the
extracted lemma's hypothesis matches; the `intro c' hc'` at the top of `deeperFlagGood_finite_impl` already
opens that quantifier, so the extraction boundary is exactly the `suffices`.

---

## 5. 5-HOLE DISPATCH → (□)  (T5 — the import-topology hazard lives here)

**⚠ It is a 3-way dispatch, not 5-way.** `decoratedStepHyp_dispatch : DecoratedStepHyp adm` (DecoratedStep,
holesbe, sorry-free) branches only on:
```
by_cases hkey : M 1 < deepTailMin M
  · WAIST: hM1: M1=1 → deeperFlagWaistM1_finite (e, FILLED) | else → deeperFlagWaist_finite (c)
  · GOOD (deepTailMin M ≤ M1)          → deeperFlagGood_finite (d)
```
(a) `deeperFlagStrictShell_finite` and (b) `deeperFlagSaturatedShell_finite` are NOT dispatch cases — they
are the per-shell inputs `hstrict`/`hsat` consumed *inside* (d) `deeperFlagGood_finite_impl` (and the crux
covers both; see below). The 5 hole-theorems and their discharge:

| Hole | DecoratedStep stub | Discharged by | Source |
|---|---|---|---|
| (e) M₁=1 | `deeperFlagWaistM1_finite` @386 | **FILLED** in DecoratedStep | holesbe |
| (c) waist M₁≠1 | `deeperFlagWaist_finite` @343 | `WaistConnector.deeperFlagWaist_finite_impl` + O1 `hred` | waist |
| (d) good | `deeperFlagGood_finite` @318 | `GoodConnector.deeperFlagGood_finite_impl` + O1 + hstrict/hsat/hsector | good |
| (a) strict shell 1≤j<r | `deeperFlagStrictShell_finite` @254 | `deeperFlag_shell_le` (DeeperFlagCore) + `hIH` | brickF/step2 crux |
| (b) saturated shell j=r | `deeperFlagSaturatedShell_finite` @279 | `deeperFlag_shell_le` at j=r (corank-trivial) + `hIH` | brickF/step2 crux |

⚠ **(b) contradiction — RESOLVED as stale docstring.** DecoratedStep's (b) docstring says it carries "the
SAME unbuilt outer double induction … beyond a bounded fill on this tide." This is **stale (pre-cruxfin)**:
`deeperFlag_shell_le` takes `hj : j ≤ min(M0−t)(M1−t)` (allows j=r) and concludes `shellSpineIntegrand ≤
C·comparator.integral` uniformly; at j=r the corank `min(a,b)=0` (S3 corner drops) but the pivot route
still applies — the ledger's "crux is the shared engine for (a)[off-sector]/(b)[j=r]/(ii)[j=0-borderline]"
supersedes the docstring. **Flag to verify at rendezvous:** confirm `deeperFlag_shell_le` closes at the
j=r `min(a,b)=0` degeneracy (should, via `peelCharge = ab = 0`, `hc' : 0 < c'`). `hsector` (j=0) is the
#120 `sjSector` a+b≤M2 sub-case + the a+b=M2+1 borderline crux — also controller-supplied at rendezvous.

**⚠⚠ IMPORT-TOPOLOGY HAZARD (T5) — the dispatch cannot be completed in place.**
- `WaistConnector` **imports `RouteMSJDecoratedStep`** and calls `deeperFlagGood_finite` (the DecoratedStep
  (d) stub) on `rev M`. So WaistConnector is DOWNSTREAM of DecoratedStep.
- `GoodConnector` does NOT import DecoratedStep (parallel/upstream-eligible).
- DecoratedStep's `decoratedStepHyp_dispatch` needs (c) filled, whose impl is in WaistConnector (downstream)
  ⟹ filling (c) in DecoratedStep in place would **cycle**.

**Resolution (same relocate+rehome pattern as the mint):** RE-HOME the final assembly (`decoratedStepHyp_dispatch`
→ `DecoratedStepHyp adm`, and the `DecoratedDescent` witness) into a NEW file DOWNSTREAM of GoodConnector +
WaistConnector + the crux, referencing the connector `_impl`s directly (with O1 `hred`, crux `hstrict/hsat/
hsector`) rather than the DecoratedStep stubs. Alternative: refactor WaistConnector to call
`GoodConnector.deeperFlagGood_finite_impl` directly (GoodConnector doesn't import DecoratedStep), drop its
`RouteMSJDecoratedStep` import, then DecoratedStep can import both connectors and fill (c)/(d) in place. The
re-home is lower-risk; decide early — it sets the final file layout.

**Chain to (□):** `decoratedStepHyp_dispatch : DecoratedStepHyp adm` + `decoratedBaseHyp_faithful :
DecoratedBaseHyp adm` (#4, RouteMSJBaseHyp:395, sorry-free ✓) + `adm_trivial` (RouteMSJAdm:211 ✓) →
`DecoratedDescent := ⟨adm, adm_trivial, decoratedStepHyp_dispatch, decoratedBaseHyp_faithful⟩` →
`routeMBoxThresholdFinite_of_decoratedDescent` (RouteMSJDecoratedRec:216, canonical clean-three) →
`∀ n M, RouteMBoxThresholdFinite M`. Every hypothesis sources from a landed piece (no dangling hyp),
modulo T1–T5.

---

## 6. MINT #108

`aoyagi_learning_coefficient` was re-homed by mintrehearse to `HeadlineL1Mint` (Skeleton→prestage is a
cycle). On the mint branch (2dc2682a):
- `Skeleton.lean`: `aoyagi_learning_coefficient` → renamed **`aoyagi_learning_coefficient_legacy`** (body
  unchanged, retains its 5 sorryAx via the D1▸L2 rungs).
- `HeadlineL1Mint.aoyagi_learning_coefficient` (re-homed) — the ONLY real sorry is @106:
  `have hDescent : DecoratedDescent := sorry`, then `exact aoyagi_learning_coefficient_prestage hDescent …`.
  `_prestage` (L=1 → `_L1`; L≥2 → `RouteMSJMint.aoyagi_learning_coefficient_gen_of_descent`) and `_L1` are
  sorry-free.
- **MINT = replace HeadlineL1Mint:106 `sorry` with `⟨adm, adm_trivial, decoratedStepHyp_dispatch,
  decoratedBaseHyp_faithful⟩`** (or the re-homed dispatch from T5).
- `_gen_of_descent` applies (□) at **`M = fun s => H s − r`** and needs `hL2 : 2 ≤ L`; the DecoratedDescent
  gives `∀ M`, so it covers `H − r` — no gap.

**Universe check (fibre-θ-univ-zero lesson): CLEAR.** The headline statement `(⨅ w ∈ optimalSet H B,
rlctAt H (dlnLoss H B) w) = ENNReal.ofReal (aoyagiLambda H r)` is fully concrete Type 0 (`H:Fin→ℕ`,
`B:Matrix ℝ`, `rlctAt→ℝ≥0∞`); no universe polymorphism, so the whnf-timeout/`Type u` vs `Type 0` trap does
not bite this mint. (The re-homed statement is byte-identical to the legacy per mintreview.)

**TRUE-MINT cleanup** (controller taste, per mintreview): delete `aoyagi_learning_coefficient_legacy` +
dead D1▸L2 rungs; drop the rehearsal harness `MintRehearsal108.lean` (1 sorry, untracked); author ONE final
`AxCheck.lean` (single-writer) with the audit entries harvested from brickF + mint. The final gate = forced
`#print axioms aoyagi_learning_coefficient` clean-three (no `sorryAx`, no `cited_aoyagi` — the cited-Aoyagi
equality lives only in the separate RlctPayoff framing, not in this `_gen ∘ descent` route).

### 6b. NON-VACUITY GATE — the headline has content (O2-review catch, VERIFIED, no gap)

⚠ **The vacuity trap.** `RouteMBoxThresholdFinite M := ∀ c':NNReal, (c':ℝ) < (minAdm M)/2 →
routeMLayerBoxIntegral M c' 1 < ⊤` (`RouteMBoxReduction.lean:165`) is **vacuously true when `minAdm M = 0`**
(no `c':NNReal` is `< 0`). So the (□) is a mix of vacuous (degenerate M) + substantive (nondeg M) instances
— fine for the `∀M` box-finiteness, but the #108 HEADLINE must land on a SUBSTANTIVE instance, else the
finiteness it consumes has no content.

**(a) The headline's nondeg hypothesis.** `aoyagi_learning_coefficient` carries `hpos : ∀ s : Fin (L+1),
r < H s` and `hL : 1 ≤ L`. `_gen_of_descent` applies (□) at **`M = fun s => H s − r`**, so `hpos ⟹
∀ s, 0 < M s` and `1 ≤ L` — exactly a nondegenerate width vector with a genuine layer.

**(b) The `nondeg ⟹ minAdm ≥ 1` fact IS banked for the FULL M** (not redChain-only):
`R1ResolutionGeneral.one_le_minAdm_of_pos_general (M : Fin (L+1)→ℕ) (hL : 1 ≤ L) (hMpos : ∀ s, 0 < M s) :
1 ≤ minAdm M` (canonical @98; also on step2). Proof = `one_le_minAdmRec_of_pos` (the all-`L` layer-peeling
recursion, `minAdmRec_eq_minAdm`) — genuine for the whole chain, every arity. Plus the 3-width
`R1ResolutionInterfaceL2.one_le_minAdm_of_pos (M : Fin 3) (∀ s, 0 < M s) : 1 ≤ minAdm M`.
⚠ **Do NOT reach for rhsfin's `RouteMSJPivotFin.{one_le_minAdm_redChain, one_le_minAdmRec}`** — those are
crux-LOCAL (`minAdm(redChain u M)`/`minAdmRec`, `u≥1`), NOT the headline's `minAdm(H−r)`. The right fact is
`one_le_minAdm_of_pos_general`.

**(c) NO GAP — and it is already load-bearing (not merely latent).** `one_le_minAdm_of_pos_general` gives
`minAdm (H−r) ≥ 1 ⟹ threshold (minAdm)/2 ≥ ½ > 0 ⟹` the `c'` range `[0, minAdm/2)` is non-empty ⟹ the
box-finiteness is substantive at the headline's M. Moreover the RLCT resolution the headline routes through
ALREADY consumes it: `r1_resolution_general` opens with `have hpos : 1 ≤ minAdm M :=
one_le_minAdm_of_pos_general M hL hMid`, and `_gen_of_descent` passes `hpos` into `_gen` alongside the (□)
term. So the mint just supplies the (□) witness; non-vacuity is preserved by the existing `_gen` proof —
**not a new mint obligation.** Mint-fidelity CHECK (cheap, do at the gate): confirm the minted headline's
`#print axioms` shows the RLCT-equality content (not a vacuous collapse); record in the AxCheck prose that
#108's nondeg (`r < H s`) ⟹ `minAdm(H−r) ≥ 1` (via `one_le_minAdm_of_pos_general`) is what makes the
headline non-vacuous.

---

## 7. LESSONS / PITFALLS that bite the rendezvous

- **⚠ Stale local refs.** `git fetch origin` first; integrate from `origin/genm-sj5-step2` (e395121c) and
  `origin/genm-sj5-waist` (cf47a1a9), not the stale local branch refs. (lessons.md: "git-fetch the peer
  branch BEFORE reviewing", "divergent file copies → phantom disagreement".)
- **⚠ Isolation-cd hazard.** An `isolation:worktree` spawn can reset/switch the MAIN checkout's branch and
  strand controller commits (lessons.md 879/905/916; endgame "Process" section). Commit+push before any
  spawn; `git branch --show-current` must be `expedition/aoyagi-full` after every tide launch; NEVER run an
  absolute-cd `git reset --hard` from a worktree. (waistdec already tripped this once — self-restored.)
- **⚠ Stale-olean AxCheck.** After `cp`/checkout of a file into the tree, `scripts/lb DLNFibre` can serve a
  STALE olean → spurious/absent `sorryAx`. Force-rebuild the module (`find .lake/build -name '<Mod>.olean'
  -delete` + rebuild) before trusting `#print axioms` (lessons.md 2026-06-25). Apply to every authoritative
  file copied in, especially the crux + O2 + the mint.
- **⚠ prodAux cast trap (retired for O2, watch for re-use).** The opaque-width dependent-`Fin`-cast trap
  (`prodAux` is a PREFIX product; suffix/reversal needs `have`+`exact` at explicit `⟨_, by decide⟩`
  indices) bit the O2 `prod_revParams` build — now DONE sorry-free, so retired for O2. But any further
  prod/reindex wiring at rendezvous (e.g. if frame-stripping touches `Params`/`redChain` reshapes) hits it.
- **Green-gate gap.** `lake build DLNFibre` covers only the aggregator's transitive closure; a file not
  imported into `DLNFibre.lean` is silently unbuilt (and its sorries invisible). Wire the new files into the
  aggregator + AxCheck; the assembly gate = "sorries in the touched files == expected" not whole-tree
  (21 pre-existing tracked scaffold sorries). Run ONE full `scripts/lb DLNFibre` + AxCheck at the mint.
- **Chart/CoV soundness (for the O1/O2 audits).** A factorization-verified `cov` can still assert `0=⊤` via
  a null-image chart (the phi334 lesson) — footprint looks normal. O2's `routeMLayerBoxIntegral_comp_rev`
  is a measure c-o-v; the commissioned cruxreview should confirm the reversal permutation is a genuine
  measurable embedding (it is `Fin.revPerm` + transpose — benign, but confirm InjOn/non-null).

**Dead / ruled-out routes to avoid:** SVD-qPeel / Schur-chart / `waistCharge` for the waist (superseded by
the reversal-CoV + (d)-on-rev-M route; the 3 orphan files carry sorries — DROP, don't wire). Route-(b)
drop-front eigenvalue-profile weight (non-admissible, red herring). The `hcvg`/frame apparatus as live
math (dead — vestigial; see T3). In-place fill of the DecoratedStep (c) stub (import cycle; see T5).

---

## Appendix — exact locations (for handing straight into the tide spec)
- Crux: `RouteMSJPivotFin.{pivotPeel_domination@1240, forward_LHS_finiteness@1280, pivotDom_finiteness_impl@1313,
  pivotDomRHS_ne_zero_aux@757, pivotDomRHS_eq_top_of_critical@1073}` (step2 e395121c).
- Stubs to wire: `RouteMSJPivotDom.{pivotDom_finiteness@74, pivotDom_RHS_ne_zero@96, pivotDom_uzero@109,
  headSplit_pivotDom_impl@122}`; `RouteMSJHeadSplitDom.{headSplit_pivotDom@85, shellSpine_le_hsQ_box@210,
  headSplit_domination_impl@238}` (step2 e395121c). `shellSpine_le_hsQ_box` FILLED (non-shell) on assembly ea55126a @326.
- D-stub: `RouteMSJDeeperFlagCore.{headSplit_domination@513(sorry@549), deeperFlag_spineToCore@655,
  deeperFlag_shell_le@750, deeperFlag_shell_core_le@368, exists_headSplitFrame@492}` (brickF 759fcf72).
- Connectors: `RouteMSJGoodConnector.deeperFlagGood_finite_impl@331` (O1 `suffices hbox`);
  `RouteMSJWaistConnector.deeperFlagWaist_finite_impl` (`hred`) + `deepTailMin_rev_le_of_waist`;
  `RouteMSJWaistReversalCoV.{routeMLayerBoxIntegral_comp_rev, routeMBoxThresholdFinite_of_rev, prod_revParams}`.
- Dispatch/driver: `RouteMSJDecoratedStep.{decoratedStepHyp_dispatch@553, deeperFlag{Strict@254,Saturated@279,
  Good@318,Waist@343,WaistM1@386}Shell?_finite}` (holesbe); `RouteMSJDecoratedRec.{DecoratedDescent@206,
  routeMBoxThresholdFinite_of_decoratedDescent@216}` (canonical); `RouteMSJAdm.{adm@194, adm_trivial@211}`;
  `RouteMSJBaseHyp.decoratedBaseHyp_faithful@395`.
- Mint: `HeadlineL1Mint.{aoyagi_learning_coefficient@99(sorry@106), _prestage@77, _L1@41}`;
  `RouteMSJMint.aoyagi_learning_coefficient_gen_of_descent`; `Skeleton.aoyagi_learning_coefficient_legacy@1689`.
