# Statement card — general-`L` interior-chart injectivity (`genm-glift` injOn half)

> **Claim.** For every depth `L > 0`, dimension vector `M : Fin (L+1) → ℕ`, and the achiever descent
> path `tach M` with `ha : StructAdm M (tach M)` (plus `0 < Text M (tach M) L`, `0 < Wext M L`), the
> general-`L` interior chart `interiorLivePhiGen` is **injective** on the all-coords-nonzero domain
> `interiorLiveInjDomGen` (`{u | u leafPivot ≠ 0 ∧ ∀ j, u j ≠ 0}`). This closes the last residual of
> the general-`L` interior-chart lift — the `BchartLeafGen`-recovery half.
>
> - **Lean:** `DLNFibre.DLN.RLCT.interiorLive_injOnGen` and its residual atom
>   `interiorLive_BchartLeaf_injOnGen`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveGenInj.lean`), via the recovery
>   `DLNFibre.DLN.RLCT.BchartLeafGen_injOn_recover`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveGenInjRec.lean`) and the shared gate
>   `DLNFibre.DLN.RLCT.detK_ne_zero_gen`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveGenSchurGate.lean`)
>   @ `<pending — genm-glift push SHA onto 9963b788>`.
> - **Gloss.** `Set.InjOn (BchartLeafGen M ha)` on the `kLDU ∘ pivotBlowupOn`-image of the injectivity
>   domain: two points whose boundary-factor charts agree are equal. Equivalently `interiorLive_injOnGen`:
>   `Set.InjOn (interiorLivePhiGen M ha hL h0r h0c) (interiorLiveInjDomGen …)`.
> - **Proved.** UNCONDITIONALLY (∀`L`): the value-map recovery. From `BchartLeafGen y = BchartLeafGen y'`,
>   peel `paramsEquivFlat` (injective) + the banked `reindexLs_BparamsLeafGen` ⟹ `Agen 1 (B y) s =
>   Agen 1 (B y') s` at every boundary `s : Fin L`. Per boundary, `chainA`'s `natAdd` rows give `Wblk s`
>   and its `castAdd` rows give `Cgen(s+1) − Nblk s·Wblk s`; a forward induction over `s` (triangular,
>   `layer s ← layer s−1` via `Nblk s = readN⟨s−1⟩`) recovers `Cgen(s+1)`. Interior `Cgen(s+1) =
>   schurFrameProd(readK/X/N/E⟨s⟩)`, bridged to `schurFrameMap` (`flatBlock_schurFrameMap_eq_gen` +
>   `flatBlockLE.injective`) and inverted by `schurFrameMap_inj_of_det_ne_zero_gen` given `det K_s ≠ 0`;
>   the leaf `Cgen(L) = rfinDirectGen`. A `funext q; cases chartIdxEquiv q` reassembles the per-boundary
>   reader equality to `y = y'` (lift slots ↦ `readW`, interior frame slots ↦ `readK/X/N/E` via
>   `frameSplitEquiv`, leaf boundary `L−1` frame slot ↦ `rfinDirectGen` via `schurSlotEquiv`).
> - **Assumed.** `StructAdm M (tach M)` (the chart-coordinatization side conditions: `h0`/`hc`/`hL`/`hdesc`/
>   `hub`); `0 < L`; `0 < Text M (tach M) L`, `0 < Wext M L` (leaf-pivot well-definedness). `det K_s ≠ 0`
>   at each interior boundary is DISCHARGED on the domain (not assumed): `detK_ne_zero_gen` proves it via
>   the LDU-monomial `readK_kLDU_det = ∏ pivots`, each `= (pbo x)(diagAxis) ≠ 0` on the all-nonzero domain.
> - **Cited.** none. (Pure matrix algebra + banked reindex/equiv machinery; no external analytic input.)
> - **Deferred.** none for the injectivity half. (The interior atom's DETERMINANT half —
>   `DtotGen_abs_det` / `eihd_hD_gen` in `RouteMInteriorLiveGenDet`, factor1's Route-B — is a SEPARATE,
>   still-open piece; it is NOT part of this card's claim. The domain-match between this injOn and the
>   det side is checkable only once both halves assemble — the controller commissions that fidelity
>   review on the assembled interior atom, not here.)
> - **Route.** Route (a), slot-disjoint faithful decode, eInGen-FREE (independent of the `eihd_hD_gen`
>   det crux): the triangular forward-substitution over boundaries, the general-`L` lift of the `L = 2`
>   `interiorLive_BparamsLeaf_injOn`. The whnf opaque-matrix wall (from `rw [h]` on a dependent-width
>   `schurFrameProd` equality) is sidestepped by working on the `SchurInc` TUPLE
>   (`schurFrameMap_inj_of_det_ne_zero_gen`) + the entry-by-entry value bridge, not the block matrix.
> - **Status.** sorry-free. Forced `#print axioms` (elaboration-forced, on base `9963b788`):
>   `interiorLive_BchartLeaf_injOnGen`, `interiorLive_injOnGen`, `BchartLeafGen_injOn_recover`,
>   `detK_ne_zero_gen` — all `[propext, Classical.choice, Quot.sound]` (no `sorryAx` / `native_decide` /
>   `monomial_rlct` / S2). `scripts/lb` GenInjRec / GenInj / Gate GREEN; full `lake build DLNFibre` GREEN.
>   Fidelity review of the assembled interior atom: pending (controller-commissioned, not this thread).

## Files

- `lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveGenSchurGate.lean` (NEW, 76 LoC) — shared gate:
  `interiorLiveInjDomGen`, `detK_ne_zero_gen`.
- `lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveGenInjRec.lean` (REPLACES chart's 4-sorry skeleton,
  531 LoC) — the route-(a) recovery, UPSTREAM of `GenInj`.
- `lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveGenInj.lean` (MODIFIED) — imports `GenInjRec`,
  local `interiorLiveInjDomGen` removed (now in the gate), `interiorLive_BchartLeaf_injOnGen` sorry
  filled with `BchartLeafGen_injOn_recover`.

Import direction: `GenInjRec` (upstream, imports `GenDet` + `GenSchurGate` + `HmapGen` + `ProjV0Gate` +
`FlatBlockLE`) → `GenInj` (downstream, imports `GenInjRec`). None of these three files touch `GenDet`'s
open sorries; they consume only its sorry-free `Agen` / `Cgen` / `genBlkFlatLive` / `reindexLs` parts.
