# Statement card — live-decoder locality (b-0 lifted to genBlkFlatLiveR1), `genm-detcomp`

> **Claim (hbt sub-piece 1a).** The value-level off-block-vanishing `Agen reads only layers ≤ s` holds
> for the LIVE decoder `genBlkFlatLiveR1` (not only the dead-leaf `genBlkFlatStruct`), given the leaf
> reader agrees (`rfinx = rfiny`).
>
> - **Lean:** `DLNFibre.DLN.RLCT.Agen_genBlkFlatLiveR1_reads_le` (+ `genBlkFlatLiveR1_Rmat_indep`)
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMLiveLocality.lean` @ `<pending — off genm-detcomp e7604aac>`)
> - **Gloss.** If `∀ q, bLayer M t ha q ≤ s → x q = y q` and `rfinx = rfiny`, then `Agen u M t
>   (genBlkFlatLiveR1 … rfinx x) hle s = Agen u M t (genBlkFlatLiveR1 … rfiny y) hle s`.
> - **Proved (unconditional, sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`):** both,
>   mirroring `Agen_genBlkFlatStruct_reads_le` with the live-decoder deltas handled —
>   - `Bmat`/`Nblk`/`Wblk` = struct's (their `_indep_of` lemmas carry verbatim);
>   - `Rmat (j+1)` = `Function.update (struct.Rmat) p (const)`: `update_self` at `j+1 = p` (fixed const),
>     `update_of_ne` → `genBlkFlatStruct_Rmat_indep_of` else;
>   - leaf `Cgen L = u·Rfin L = u·rfin`: `subst (s+1 = L)` (from `s < L`, `¬ s+1 < L`) then `Rfin L = rfin`
>     (full `simp [genBlkFlatLive]`), closed by `hrfin`.
> - **Assumed.** `hrfin : rfinx = rfiny` — the leaf reader's layer-locality (the budget-piece reader
>   supplies it; the same parametrization the chart's `rfin` argument already carries).
> - **Cited.** none.
> - **Deferred (hbt sub-piece 1b — the next step):** the OUTPUT-coord ↔ layer bridge. `hloc`
>   (`toMatrix_blockTriangular_of_locality`'s hypothesis) needs `phiFlatLiveR1`'s flat OUTPUT coord `i`'s
>   invariance under input coord `j` for `bLayer i < bLayer j`. `phiFlatLiveR1 v i = paramsEquivFlat
>   (chartParamsGen …) i`; the flat output coord `i` sits at the Params-component `s = bLayer i` (the
>   `paramsPack_layer` bridge: `paramsEquivFlat`'s coord indexing ↔ `chartIdxEquiv`/`bLayer`). Given that
>   bridge, `Agen_genBlkFlatLiveR1_reads_le` (this card) supplies the value invariance ⟹ `hloc` ⟹ (with
>   `phiFlatLiveR1_differentiableAt`) `hbt` via `toMatrix_blockTriangular_of_locality`.
> - **Status.** sorry-free, axiom-clean (forced `#print axioms`) — awaiting reviewer.
