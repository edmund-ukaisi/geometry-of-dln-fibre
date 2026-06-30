# genm-r1lower — R1-LOWER interior achiever box-divergence (LIVE+kLDU)

**Target:** the `hInterior` atom for the L=2 R1-LOWER dispatch spine —
`∫⁻_{cubeBox N ε} |routeMCore M|^{−c'} = ⊤` for `c' ≥ ½·minAdm`, on the interior class. Feeds
`routeMCore_box_diverges_achiever_spine` → `cover_ge_div` (R1-LOWER value).

## Architecture (LIVE+kLDU, NOT dead-leaf)

The dead-leaf decoder `phiFlatLDU = genBlkFlatStruct ∘ kLDU` (`RouteMInteriorLDUContract`) is
**NON-INJECTIVE** (genm-hinj: radial enters only as `u•Rmat`, `(u,readE)↦(λu,readE/λ)` invariant) —
its `cov.hinj` is false. **RETIRED.**

The CORRECT chart is the LIVE-leaf `phiFlatLiveAt` (with the `rfinFixedPivot` `(0,0)=1` anchor →
injective) **precomposed with `kLDU`** (monomializes the K-frame det). Pivot = `leafPivot` (a leaf
slot), NOT `structPivot = ⟨0⟩`. Built in `RouteMInteriorLiveContract.lean`.

**Double-count avoidance** (Codex xhigh verdict, `codex/livekldu-fork-answer.md`): push `kLDU` into
the boundary factor — `B' = BchartLeaf ∘ kLDU`, so `radialComp_abs_det_at` fires ONCE. Hinges on the
COMMUTE `pivotBlowupOn activeM leafPivot ∘ kLDU = kLDU ∘ pivotBlowupOn activeM leafPivot` (source-
verified: `activeM = {E-block ∪ leaf}`, NO K-slots; `kLDU` touches only K).

## Status (`RouteMInteriorLiveContract.lean`, builds GREEN)

CLOSED (sorry-free):
- `routeMCore_interiorLivePhi` — rate `(x leafPivot)²·U` via `phiFlatLiveAt_rate ∘ kLDU` + `kLDU_leafPivot`.
- `kLDU_leafPivot` — radial survives `kLDU` (leaf-boundary K-block `0×0` at L=2 → identity arm).
- `kLDU_eq_on_activeM` — `kLDU` identity on E-block + leaf slots (the shared commute atom).
- `readK_pbo_all` — `pbo` fixes K-slots ∀ boundary (boundary 0 banked, leaf vacuous).
- `interiorLive_commute` — the load-bearing map fact (funext: pivot / activeM / spectator casework).
- `interiorLive_leafH` + `_pivot` — H2 exponent vector (`liveLeafHOnIdx` K-diag placement + leafPivot override).
- `interiorLive_cov` — assembled from the banked `ldu_cov_of_differentiable_injOn` engine (given diff/abs_det/injOn).
- bundle `interiorLiveNodeChart` + atom `routeMCore_box_diverges_interiorLive` — wired (sorry-gated on the below).

CLOSED (cont.): `differentiable_kLens` / `_kLDU` / `_pivotBlowupOn` atoms; `interiorLive_diff` (via
hmap-for-B' factorization → composition); `interiorLive_E`; cov engine extracted to standalone
`RouteMNullSliceCov.lean` (LIVE contract decoupled from the retired dead-leaf trio — orphan, clean).

OPEN obligations — 5 left, 2 substantive + 3 handed off:
- `interiorLive_abs_det` (H2 keystone) — SPINE verified bounded (hmap-for-B' via commute +
  `radialComp_abs_det_at`). The ONE heavy piece: the det bookkeeping
  `|det D(BchartLeaf∘kLDU)| = ∏_{K-diag}|q|^{(r+c)+2(t−1−i)}` (dead-leaf H2b — Schur·LDU det telescope;
  banked partial `interiorDet_leaf_headline_Bchart`). DIRECTION-REQUEST pending (solo vs sub-hand).
- `interiorLive_injOn` (the NAMED RISK, BOUNDED read) — factors through the composition: `pivotBlowupOn_injOn`
  (banked) + `kLens`/`lduCoreMap` injectivity off q-pivots (LDU recovery, NEW but single-block) +
  `BchartLeaf` injectivity (opaque-width chart-param recovery — the genuine content, composition-factored
  so far cheaper than the monolithic `chartParams3333_injOn`). NO banked BchartLeaf/kLens inj yet.
  flag-at-2-cycles armed.
- `interiorLive_Ubound` / `_Umeas` / `_image` — handed to genm-ubound (route-independent).

## injOn-∀M read: BOUNDED (composition factoring; the monolithic 27-coord `chartParams3333_injOn` NOT needed).
