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

CLOSED (cont.) — BOTH KEYSTONES ASSEMBLED sorry-free (reduce to named parallel-hand atoms):
- `interiorLive_abs_det` (H2 keystone) — `radialComp_abs_det_at` (hmap-for-B' via commute + hasDB'
  composition) → `|u leafPivot|^{minAdm−1}·|det DB'|`, then `interiorLive_BdetMonomial` + the
  `Finset.prod`-split-at-pivot arithmetic. Sorry-free modulo the atom.
- `interiorLive_injOn` (#3 glue) — `Set.InjOn.comp` chain (pbo banked + the 2 sub-atoms). Sorry-free
  modulo the atoms. `interiorLiveInjDom` names the domain.

## 4-hand split — the 6 remaining sorries are EXACTLY the parallel-hand atoms + my injOn#2:
- `interiorLive_BdetMonomial` ← **genm-h2bdet** (det monomial, slot shape:
  `|det D(BchartLeaf∘kLDU)(pbo u)| = ∏(if j=leafPivot then 1 else |u j|^{leafH j})`).
- `interiorLive_kLDU_injOn` ← **genm-lduinj** (kLDU inj on `pbo''injDom`, via LDU-product uniqueness).
- `interiorLive_BchartLeaf_injOn` ← **ME (injOn#2)** — the off-radial block recovery (K via LDU, X via
  fwd-subst K⁻¹, N/E/leaf linear, then `paramsEquivFlat`). The genuine remaining content on my side.
- `interiorLive_Umeas` / `_Ubound` / `_image` ← **genm-ubound** (route-independent).

spine→cover_ge_div: my atom `routeMCore_box_diverges_interiorLive` is the `hInterior` provider; the
binding `routeMCore_box_diverges_achiever` (RouteMLayerCoverGE.lean, NOT my file) is the controller's
integration with my atom + genm-r1smeared's `hSmeared_L2` + structural facts.

## injOn-∀M read: BOUNDED (composition factoring; the monolithic 27-coord `chartParams3333_injOn` NOT needed).
injOn build skeleton in `injon-skeleton.md`; Codex scope verdict in `codex/injon-scope-*`.
