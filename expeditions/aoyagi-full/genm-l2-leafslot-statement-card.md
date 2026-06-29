# Statement card — ∀M-L2 interior-det: leaf-slot core + chart + headline interface

**Thread:** genm-detfderiv (leaf-pivot decoder). **Date:** 2026-06-29. Branch `genm-detfderiv`
(pushed to `origin`). Axiom footprint everywhere: `[propext, Classical.choice, Quot.sound]` (forced
`#print axioms`). Clean-three on all three files (zero warnings, longLine ≤ 100 codepoints).

## What was delivered (Proved, sorry-free)

Three new modules, all building green with zero sorry/axiom/native_decide.

### `lean/DLNFibre/DLN/RLCT/Validate/RouteMLeafSlot.lean`
The combinatorial core (decoder-agnostic) + **the binding (3,3,4) gate**.
- `leafSlot M t ha hL i j : Fin (routeMAmbient M)` — the leaf-residual flat-slot embedding. Reads the
  ChartIdx **Schur block at boundary `L − 1`**, whose dimension `schurDim (L−1) = Text L · Wext L`
  matches the leaf size. (Resolves the cert addendum's open leaf-slot-routing sub-design: the leaf
  reuses the boundary-`(L−1)` Schur slot, which the interior decoder's `Bmat L`/`Nblk L` "waste"
  because the leaf arm `Cgen L = u·Rfin` overrides them.)
- `leafSlot_inj` — injective in `(i,j)`.
- `leafSlot_ne_activeSlotE` — leaf slot ≠ E-block slot at a distinct ChartIdx boundary.
- `activeM M ha = activeEImg ∪ activeLeafImg` (L = 2): the structured residual active set.
- `activeM_card : activeM.card = minAdm M` (L = 2) — disjoint `card_union`,
  `(Text 1 − Text 2)·(Wext 1 − Text 2)` (interior E-block `= rBlock 0 · cBlock 0`) plus
  `Text 2 · Wext 2` (leaf `= rBlock 1 · cBlock 1`, equal via `tStar_last_eq_zero`), summing to
  `minAdm` by the banked Aoyagi bridge `sum_rBlock_cBlock_eq_minAdm`.
- **`activeM_card_334 : (activeM (![3,3,4])).card = 8`** — the VALIDATE-(3,3,4) GATE. **PASSES**:
  interior E-block `2×2 = 4` + leaf `1×4 = 4` = `minAdm = 8` (the `minAdm = 8` by `decide`). Matches
  the HONEST `(3,3,4)` chart radial exponent `minAdm − 1 = 7` (`leafH334 0 = 7`,
  `RouteMLayerCoverGEL2`). NO count/spread mismatch.

### `lean/DLNFibre/DLN/RLCT/Validate/RouteMLeafChart.lean`
The achiever chart on the LIVE-leaf decoder (NOT the R1 override — the named bug).
- `rfinFixedPivot M ha hL x` — the leaf reader: `(0,0) ↦ 1` (the fixed radial pivot), off `(0,0) ↦`
  the leaf coordinate `x (leafSlot i j)`. (`rfinFixedPivot_pivot` / `rfinFixedPivot_off`.)
- `leafPivot M ha hL h0r h0c = leafSlot … 0 0` — the radial pivot slot.
- `phiFlatLiveAt M ha hL p₀ x = phiGen (x p₀) M tach (genBlkFlatLive … (rfinFixedPivot x) x) hle` —
  the chart. **No E-block override** (the interior E-block reads `readE` from `x`).
- `phiFlatLiveAt_rate : routeMCore M (phiFlatLiveAt … x) = (x p₀)²·V` — the decoder-agnostic rate
  (via `routeMCore_phiGen` + the live identity-boundary `hC0_live`).
- `leafPivot_mem_activeM : leafPivot … ∈ activeM M ha` (L = 2).

### `lean/DLNFibre/DLN/RLCT/Validate/RouteMLeafHeadline.lean`
The headline capstone — the count/wiring/rate CLOSED, the boundary obligations named.
- `interiorDet_leaf_headline M ha h0r h0c u B DB hmap hasDB`:
  `|det (fderiv ℝ (phiFlatLiveAt …) u)| = |u (leafPivot …)|^(minAdm M − 1) · |det DB|`.
  The network-combinatorial inputs are discharged from the banked bricks (`activeM_card`,
  `leafPivot_mem_activeM`) via `radialComp_abs_det_at`. The two named hypotheses are the genuinely
  remaining boundary-factor obligations.
- `interiorDet_leaf_headline_engine …`: the `∏_{s:Fin 2} engine s` form, with the extra
  `hdet : |det DB| = ∏ engine` hypothesis.

## What is NOT yet delivered (the precisely-scoped remaining gap)

The FULLY-discharged headline (no `hmap`/`hasDB`/`hdet` hypotheses) needs the boundary factor `B`
constructed at opaque widths:
1. **`hmap`** — the per-layer `chartParamsGen` reindex `phiFlatLiveAt … = B ∘ pivotBlowupOn activeM
   leafPivot`. The opaque-width analog of the `(2,2,2)` `chartParamsGen_Glr_eq`. Needs the explicit
   `Agen 0` (Schur frame, E = readE) and `Agen 1` (leaf-coupled `chainA`) identities at opaque
   `Text`/`Wext` widths, then `B` defined as the explicit chart reading the pivot as an ordinary
   coordinate. THE BOTTLENECK (the scoping doc's "VIABLE-BUT-HEAVY: dependent-Fin row-cast over opaque
   Text/Wext; a green-but-wrong reindex could hide here").
2. **`hasDB`** — `B` polynomial ⟹ `HasFDerivAt B DB`. Routine once `B` is built.
3. **`hdet`** — `|det DB| = ∏ engine` via the `composeFold [schur, chain, ldu]` `ChartFactor` engine
   (`foldDerivList_abs_det_perBoundary`); engine 0 = the Schur·LDU `|det K|^(r+c)·∏|q_i|^…`, engine 1
   = 1 (leaf). Codex-confirmed route (A); needs the two boundary `ChartFactor`s + their conjugating
   CLEs.

These three are the named obligations in `interiorDet_leaf_headline`. Estimated remaining: ~600–1000
lines of opaque-width dependent-Fin work (cf. the `(2,2,2)` template's 1283 lines for the EASIER R1
decoder with `2×2` literals). Recommend a dedicated tide; validate `Agen 0`/`Agen 1` on `(3,3,4)`
first.

## Caveats / level

- This is the interior-det headline (chart-Jacobian level) ONLY. Does NOT transfer to `rlct =
  ½·codim` (needs the Cited Aoyagi equality), nor close the lower-leg `rlctAtOn`.
- `tStar_last_eq_zero` (banked) is load-bearing for `activeM_card`: it makes the leaf product
  `Text 2 · Wext 2 = tStar0 · M2` equal the last Aoyagi block `rBlock 1 · cBlock 1`. Without it the
  count would not equal `minAdm`.

## Controller action needed
Wire the three modules into the aggregator `DLNFibre.lean` (single-writer; I did not edit it). Add
`activeM_card_334` and `interiorDet_leaf_headline` to `AxCheck.lean` if they become load-bearing.
