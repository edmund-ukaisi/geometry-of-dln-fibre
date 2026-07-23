# ClearedFold finisher handoff (seat-GM → finisher seat)

THE GLOBAL MOVE (#74) render. seat-GM took the unit through the full SPECIFY gate stack + the mechanical
proof tier + keystone (a)'s assembly; this doc is turn-key for the finisher to close the remaining 7 sorries
and drive to the full-green exit.

## State
- Branch `expedition/aoyagi-engine-GM` @ `bd7ce11d5` (all commits build-complete, pushed to origin).
- Module: `lean/DLNFibre/DLN/Aoyagi/ClearedFold.lean` — the whole GLOBAL MOVE (cleared trio + invariants +
  the cleared chain). Imports `Case1Wire` (green after the deletion below), `SourceClearedResid`, `MergeBoostSplit`.
- Case1Wire deletion LANDED (`2e9d817`, pure): the REFUTED-raw case11 chain removed; CAPF cherry-picked it.
- `scripts/lb DLNFibre.DLN.Aoyagi.ClearedFold` = Build completed. `lake env lean` on the file = no errors.

## PROVEN (13 declarations, do not touch)
Defs: `clearedFoldG`, `clearedFoldB`, `FoldStepInvAt_cleared`, `LastLayerInv_cleared`.
Lemmas: `couplingClear_zero`, `continuous_couplingClear`, `couplingClear_mapsTo_foldRegion`,
`clearedFoldG_root`, `clearedFoldB_root`, `couplingCoords_case11_stable`, `couplingCoords_mono_extend`,
`sourceClearedResid_extend_delta1`/`_delta0` (S2 — 25th-catch CORRECTED to the child-cleared input, proven
by pure `foldResid_extend` unfolding), `deg1SupportedOn_center_of_hslot_cleared` (cover route),
`couplingClear_parent_fixes_stepMap_child` (KEYSTONE (a) — PROVEN modulo the cert-(i) sub-lemma below).
`case1_preserves_cleared`/`case2_preserves_cleared` compile (delegating to their conjA + conjunct-B).

## THE 7 REMAINING SORRIES (with turn-key plan)

1. `canonNormalizationOf_vanishes_on_couplingCoords` (cert (i), the ONE deep piece).
   Statement: for `k ∈ couplingCoords d p`, `canonNormalizationOf d p.conState ed.pivot (couplingClear d
   (p.extend ed) u) k = 0`. pnp cert (i) `3ec969d8f` (re-ran exit 0) supplies the per-arm write pattern:
   each of `canonNormalizationOf`'s 3 branches (def at `MonumentAtlas`, the `(i)` interior Schur / `(ii)`
   layer S+1 / `(iii)` layer S−1 recoords) writes a `readEntry` product ONE FACTOR of which is a cleared
   coupling coord (`r>a_cur` ⟹ current pivot's coupling; `r<a_cur` ⟹ `a_cur>r>a_anc` ⟹ ancestor's) → 0 on
   the child-cleared locus. Render: unfold `canonNormalizationOf` (3 branch guards), for each show the
   written `readEntry` reads a coord in `couplingCoords d (p.extend ed)` (⟹ 0 under `couplingClear`), via the
   index arithmetic. Carrier-FREE. Once this lands, (a) is fully green.

2. `stepInv_child_delta0_cleared` (δ=0 append) — CARRIER-FREE, mechanical NOW.
   Mirror `Case1Wire.stepInv_child_delta0` on the cleared trio. Uses: (a) (for `clearedFoldG child` at the
   locus via the parent-clear no-op) + `sourceClearedResid_extend_delta0` (S2, proven) + `clearedFoldB` δ=0
   (no pivot factor). q' = q∘stepMap. Provable off the current proven lemmas (no carrier, no CAPF).

3. `pivot_notMem_couplingCoords_extend` (b) — CARRIER-THREADED.
   Needs `hcanon : CanonicalPivots d (p.extend ed)` (see threading below). Fresh part (pivot ∉
   belowPivotCol d ed.pivot) self-provable (pivot on-diagonal, belowPivotCol strictly-below); ancestor part
   (pivot ∉ couplingCoords d p) from the carrier's ancestor pins.

4. `stepInv_child_delta1_append_cleared` (δ=1 append) — CARRIER-THREADED.
   Consumes CAPR's `sourceClearedResid_stepMap_eq_pivot_mul` (SourceClearedResid, CAPR frontier) + the
   cleared boost-center (D) (`hdeg1`) + (b) (the pivot factor `(couplingClear child u) pivot = u pivot`) +
   (a) + S2 delta1. Mirror `Case1Wire.stepInv_child_delta1_append` on the cleared trio.

5. `realBranch_multiAffine_step_cleared` (conjunct-B) — CAPF-GATED.
   = the cleared conjunct-B descent = raw-uncapped-descent ∘ couplingClear (#78 TRANSPORTS). Consumes
   seat-CAPF's cleared (b)-twin (CapDescent, #80) at integration. Not closeable until CAPF lands.

6. `case1_conjA_cleared` — CARRIER-THREADED. Dispatch: δ=0 → (2); δ=1 case11 → (4) fed
   `MergeBoostSplit.realBranch_boostReady_case11'`; δ=1 case12 → (4) fed `deg1SupportedOn_center_of_hslot_cleared`.

7. `case2_conjA_cleared` — CARRIER-THREADED. Dispatch: δ=0 → (2); δ=1 case2 → (4) fed the cover route (Or.inr).

## THE CARRIER THREADING (before proving 3/4/6/7)
INV's `CanonicalPivots` δ-agnostic def landed at `63cb69600` (INV lane; controller integrates to the shared
lane at #73). Thread `hcanon : CanonicalPivots d (p.extend ed)` (CHILD-path — CAPR-confirmed; destructuring
it hands BOTH the IH ancestors-canonical AND the current-edge birth pin, so case2 δ=1's needed pin is
included and case11 is trivially True) onto: (b), `stepInv_child_delta1_append_cleared`, `case1_conjA_cleared`,
`case2_conjA_cleared`, `case1_preserves_cleared`, `case2_preserves_cleared` (+ the LastLayerWire re-points).
Plain `CanonicalPivots d p` only where there is no current edge. One-line elder folded-pass note on the
touched statements. (S2/(a)/cover/mono/roots/region are carrier-FREE — do not thread.)

## CONSUMER RE-POINTS (per-file go GRANTED; DELTA-2/4 riders)
- Case1Wire: DONE (deletion `2e9d817`).
- CaseStepAssembly: re-point `case1_preserves_stepInv''`/`case2_preserves_stepInv''` to
  `ClearedFold.case1_preserves_cleared`/`case2_preserves_cleared` → returns `FoldStepInvAt_cleared`. Rider:
  the kept name's docstring FIRST sentence names the cleared output (name=content).
- LastLayerWire :139/:145: re-point `lastLayer_conjA`/`lastLayer_clear_preserves'` to the cleared route
  (`LastLayerInv_cleared` + the cleared append; the born-unit at 0 transports since `couplingClear 0 = 0`).
- MonumentAssembly `leaf_stepInv_of_path'`: the `have _hc1 := …''` binding shifts type (unused, sorried
  body) — expect no substantive edit. PROVENANCE layer stays raw (registered #81; not this unit).

## EXIT GATE
Full worktree `scripts/lb` green; forced `#print axioms DLNFibre.DLN.RLCT.aoyagi_learning_coefficient_L1`
= `[propext, Classical.choice, Quot.sound]` (L1 avoids the summit — my re-point does NOT touch its footprint;
the dirty intermediate roots `case1_preserves_stepInv''`/`exists_coreResolution` carry sorryAx from the
named frontiers 1/5 + CAPR's/CAPF's). Census: account each sorry by named frontier. Cordon: no native_decide.
Canonical merge = controller (#73).

## REFERENCE
Frame: `global-move-render-frame.md`. Certificate: `capstone-invariant-certificate.md`. Ruling: §7-§9 of
`capstone-object-ruling.md` (§10 = the cross-ref-honesty / RLCT-equivalence reading — keep it in docstrings).
pnp certs: (i)/(ii) `3ec969d8f`, cap-transport `f3d6fcbb4`. GM commits: `52fed0330`→`bd7ce11d5`.
