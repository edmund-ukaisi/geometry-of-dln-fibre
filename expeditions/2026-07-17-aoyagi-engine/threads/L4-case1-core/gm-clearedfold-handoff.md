# GM → finisher handoff: ClearedFold (THE GLOBAL MOVE, #74)

seat-GM's last act (fresh-seat accepted). Branch `expedition/aoyagi-engine-GM` @ `674a07c8a` (base
`1388f6192`); module `lean/DLNFibre/DLN/Aoyagi/ClearedFold.lean`; every commit build-complete + pushed.
Supersedes the earlier `clearedfold-finisher-handoff.md`.

## (1) LANE STATE — file-by-file

`ClearedFold.lean` (imports `Case1Wire` [green after the deletion], `SourceClearedResid`, `MergeBoostSplit`):

PROVEN (13; do NOT touch):
- defs: `clearedFoldG`, `clearedFoldB`, `FoldStepInvAt_cleared`, `LastLayerInv_cleared`.
- `couplingClear_zero`, `continuous_couplingClear`, `couplingClear_mapsTo_foldRegion` (region/continuity, controller delta-1).
- `clearedFoldG_root`, `clearedFoldB_root` (root reductions).
- `couplingCoords_case11_stable`, `couplingCoords_mono_extend` (couplingCoords structural).
- `sourceClearedResid_extend_delta1`, `sourceClearedResid_extend_delta0` (S2 — 25th-catch CORRECTED to the
  child-cleared input; proven by pure `foldResid_extend` unfolding).
- `deg1SupportedOn_center_of_hslot_cleared` (cover route; residual-agnostic mirror of the raw).
- `couplingClear_parent_fixes_stepMap_child` (KEYSTONE (a) — PROVEN, 0 sorries in its body, modulo the
  cert-(i) sub-lemma in §2).
- `case1_preserves_cleared`, `case2_preserves_cleared` (compile, delegating to conjA + conjunct-B).

SORRIED (7; the finisher's targets): `canonNormalizationOf_vanishes_on_couplingCoords`,
`pivot_notMem_couplingCoords_extend`, `stepInv_child_delta0_cleared`, `stepInv_child_delta1_append_cleared`,
`realBranch_multiAffine_step_cleared`, `case1_conjA_cleared`, `case2_conjA_cleared`.

OTHER FILES: `Case1Wire.lean` — the REFUTED-raw case11 chain DELETED (commit `2e9d8175`, pure; CAPF
cherry-picked). `CaseStepAssembly`/`LastLayerWire`/`MonumentAssembly` — NOT yet re-pointed (finisher, §4).

COMMIT TRAIL: `52fed0330` skeleton → `17707da90` case11-stable → `e33ab0607` provenance → `be2225c1a`
case2 twins → `2e9d8175` Case1Wire deletion → `a7524e78d` trivial tier → `9f55fd1ed` cover → `d9fd8b0fc`
S2 corrected+proven → `bd7ce11d5` (a) assembled → `674a07c8a` this doc.

## (2) KEYSTONE (a)'s FULL REDUCTION TRACE + the cert-(i) sub-lemma (INLINED)

`couplingClear_parent_fixes_stepMap_child` is PROVEN as: reduce `couplingClear d p (stepMap d ed v) =
stepMap d ed v` (`v := couplingClear d (p.extend ed) u`) to `∀ k ∈ couplingCoords d p, stepMap d ed v k = 0`.
Then: `hvzero` (`v` vanishes on `couplingCoords d p ⊆ couplingCoords d (p.extend ed)`) + `hshearzero` (the
edge shear vanishes on `couplingCoords d p`: **case11/rollover** `edgeShear = id` ⟹ `v k = 0` trivially;
**case12/case2** `edgeShear = blockShear ed.shearφ` ⟹ `(v + ed.shearφ v) k = v k + ed.shearφ v k = 0 +
canonNormalizationOf(…) v k` [via `hpin : ed.shearφ = canonNormalizationOf d p.conState ed.pivot` from the
`IsRealBranch` pin] `= 0` by cert (i)) + the `blockBlowupMap` 3-case split (`k=pivot`: `s pivot = s k = 0`;
`k∈center`: `s pivot * s k = _ * 0`; spectator: `s k = 0`). This is DONE.

The ONE remaining piece — `canonNormalizationOf_vanishes_on_couplingCoords`:
`∀ k ∈ couplingCoords d p, canonNormalizationOf d p.conState ed.pivot (couplingClear d (p.extend ed) u) k = 0`.
**pnp cert (i) `3ec969d8f` (re-ran exit 0) — per-arm write pattern, verbatim:**
> branch (i) interior writes `-readEntry(row, b_cur)·readEntry(a_cur, col)` and ONE FACTOR IS ALWAYS A
> CLEARED COUPLING (`r > a_cur` ⟹ the current pivot's coupling; `r < a_cur` ⟹ `a_cur > r > a_anc` ⟹ the
> ancestor's); branch (ii) writes layer `S+1` where no ancestor coupling lives; branch (iii)'s write
> vanishes by the same factor mechanism. Then `blockBlowupMap` fixes-or-scales the zero. Verified all
> edges, 3 witnesses.
RENDER: unfold `canonNormalizationOf` (`MonumentAtlas`; the 3 branch guards), and for each branch show the
written `readEntry` reads a coordinate in `couplingCoords d (p.extend ed)` (so it is `0` under `couplingClear
d (p.extend ed)`), via the index arithmetic above. Carrier-FREE. Docstring keeps the §10 cross-ref-honesty
wording (RLCT-equivalent via the source-clear rendering). ~heavy def-reading — the classic fresh-context piece.

## (3) CARRIER-THREADING SPEC
INV's `CanonicalPivots` LANDED — commit `63cb69600` on the INV lane, in the **δ-AGNOSTIC form** (the def-check
fired CAPR's contingency: divisors can be δ=0-born and the ledger adds exponents at δ=0, so the `edgeδ` guard
was DROPPED). This is strictly STRONGER than the spec'd form — your carrier statements' SHAPES are unchanged,
and the pin is available in more cases. Thread `hcanon : CanonicalPivots d (p.extend ed)` — **CHILD-path**
(CAPR-confirmed): destructuring it hands BOTH the IH (ancestors canonical) AND the current-edge birth pin in
one move, so case2 δ=1's needed pin is included and case11 is trivially True (IsRealBranch already pins it).
Plain `CanonicalPivots d p` only where there is no current edge.
THE 6-ITEM CHAIN (gain `hcanon`): `pivot_notMem_couplingCoords_extend`, `stepInv_child_delta1_append_cleared`,
`case1_conjA_cleared`, `case2_conjA_cleared`, `case1_preserves_cleared`, `case2_preserves_cleared` (+ the
LastLayerWire `lastLayer_conjA_cleared`/`lastLayer_clear_preserves'` δ=1 route). CARRIER-FREE (do NOT thread):
(a), S2, cover, `couplingCoords_mono`/`_case11_stable`, roots, region/continuity.
CROSS-LANE: this branch is off `1388f6192`, so `CanonicalPivots` is not in the worktree. Finisher's call —
thread against the NAME with the def landing at the #73 integration, OR cherry-pick `63cb69600`. One-line
elder folded-pass note on the touched statements.

## (4) REMAINING SEQUENCE
1. Thread `hcanon` (§3) onto the 6-item chain.
2. `canonNormalizationOf_vanishes_on_couplingCoords` — cert (i) render (§2). ⟹ (a) fully green.
3. `stepInv_child_delta0_cleared` — CARRIER-FREE, mechanical off (a)+S2 delta0 (q'=q∘stepMap, δ=0 no pivot
   factor; the parent StepInv applies at `stepMap(couplingClear child u)` via (a)'s no-op).
4. `stepInv_child_delta1_append_cleared` — consumes CAPR's `sourceClearedResid_stepMap_eq_pivot_mul`
   (SourceClearedResid frontier) + the cleared boost (D) (`hdeg1`) + (b) (pivot factor) + (a) + S2 delta1.
5. `case1_conjA_cleared` / `case2_conjA_cleared` — dispatch (δ=0→3; δ=1 case11→4 fed
   `MergeBoostSplit.realBranch_boostReady_case11'`; δ=1 case12/case2→4 fed the cover route).
6. `realBranch_multiAffine_step_cleared` (conjB) — CAPF-gated: consumes seat-CAPF's cleared (b)-twin
   (`CapDescent`, #80) = raw-uncapped-descent ∘ couplingClear (#78). Closes when CAPF lands.
7. RE-POINTS (per-file go GRANTED): `CaseStepAssembly.case1/2_preserves_stepInv''` → the cleared preserves
   (DELTA-4 rider: kept name's docstring FIRST sentence names the cleared output); `LastLayerWire`
   :139/:145 → the cleared last-layer route (#83; born-unit at 0 transports since `couplingClear 0 = 0`);
   `MonumentAssembly.leaf_stepInv_of_path'` have-binding shifts type (unused/sorried — expect no edit).
8. EXIT GATE: full worktree `scripts/lb` green; forced `#print axioms DLNFibre.DLN.RLCT.
   aoyagi_learning_coefficient_L1` = `[propext, Classical.choice, Quot.sound]` (L1 avoids the summit — the
   re-point is OFF its cone; the dirty roots `case1_preserves_stepInv''`/`exists_coreResolution` carry
   sorryAx from frontiers 2/6 + CAPR's/CAPF's). Census: account each sorry by named frontier. Cordon: no
   `native_decide`. Canonical merge = controller (#73).

## (5) STANDING CONSTRAINTS
- STATEMENT-LOCK: the def block + statement shapes are gate-blessed (pnp def-fidelity + elder §9). Do NOT
  restate; if a proof reveals a statement is wrong, STOP and surface (this render caught 2 statement-class
  events — O2 false laws, the 25th-catch S2 — by that reflex).
- RIDERS ALREADY APPLIED: DELTA-2 (Case1Wire deletion labelled REFUTED-raw + SUPERSEDED-BY, single fossil =
  MergeBoostSplit banner). DELTA-4 applies at the CaseStepAssembly re-point (§4.7).
- CROSS-REF HONESTY (§10): every `aoyagi-2023-worked.tex` reference states "RLCT-equivalent via the
  source-clear rendering (coordinate-form differs by our shear-frame)" — never bit-identity.
- ELDER FOLDED-PASS pendencies (controller notified, queued): the O2-revised list, the case2 twins, the
  carrier deltas, #83, the corrected S2 pair, the hcanon threading.
- PROVENANCE layer stays raw (registered #81; NOT this unit).

## REFERENCE
Frame `global-move-render-frame.md`; certificate `capstone-invariant-certificate.md`; ruling §7-§10
`capstone-object-ruling.md`. pnp: certs (i)/(ii) `3ec969d8f`, cap-transport `f3d6fcbb4`. INV CanonicalPivots
`63cb69600`. seat-GM unit-consult available via the controller.
