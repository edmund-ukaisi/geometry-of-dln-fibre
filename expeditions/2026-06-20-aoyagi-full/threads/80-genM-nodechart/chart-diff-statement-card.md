# Statement card — b-FrameM-2 assembly (1): chart-diff ⟸ per-layer Agen, `genm-detcomp`

> **Claim (b-FrameM-2 assembly step 1).** `DifferentiableAt phiFlatLiveR1 x₀` reduces to the per-layer
> differentiability of the chain layers `Agen … s.val`, via three cast-light reductions (linear reshape
> comp + Params Pi + reindex).
>
> - **Lean:** `DLNFibre.DLN.RLCT.phiFlatLiveR1_differentiableAt_of_Agen` (+ `diffAt_reindex_finCongr`)
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMChartDiff.lean` @ `<pending — off genm-detcomp 495301fe>`)
> - **Gloss.** If `∀ s : Fin L`, `fun x => Agen (x p₀) M t (genBlkFlatLiveR1 … x) hle s.val` is
>   `DifferentiableAt ℝ` at `x₀`, then `phiFlatLiveR1 M t ha hN p hp1 hp2 rfin` is `DifferentiableAt ℝ`
>   at `x₀`.
> - **Proved (unconditional, sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`):**
>   - **A** (linear CLE comp): `phiFlatLiveR1 = paramsEquivFlat ∘ chartParamsGen` (`rfl`), and
>     `paramsEquivFlat` is the LINEAR reshape (`paramsEquivFlatCLE`, banked), so `HasFDerivAt.comp`
>     reduces to `DifferentiableAt chartParamsGen`.
>   - **B** (Params Pi): `differentiableAt_pi` reduces `chartParamsGen` to its per-`s` components.
>   - **C** (`diffAt_reindex_finCongr`): the component's `finCongr`-reindex is differentiable from the
>     underlying `Agen` (each entry is an entry at a cast index — `diffAt_entry`).
> - **Assumed (the precise residual — the next sub-piece):** `hAgen : ∀ s, DifferentiableAt (fun x =>
>   Agen … s.val) x₀`. This is the per-layer chain differentiability — threading the `RouteMFrameDiff`
>   matrix-op atoms (`diffAt_matmul`/`_matadd`/`_smul`/`_read`/`_constBlock`) through `chainA`/`chainQ`/
>   `Cgen` + the decoder reads. The `finSplit`/`castAdd`/`natAdd` index decomposition (the cast-thrash
>   zone) lives HERE, not in A/B/C.
> - **Cited.** none (Mathlib calculus + the banked linear `paramsEquivFlatCLE`).
> - **Deferred.** the residual `hAgen` (above) + then b-FrameM-1 (`Frame_M`/`Q_M` + `|det Q_M|=1`) + b-1
>   (`toSquareBlock` reindex) + b-2 (per-layer det). Once `hAgen` lands:
>   `phiFlatLiveR1_differentiableAt_of_Agen` ⟹ `DFrame_M` exists ⟹
>   `toMatrix_blockTriangular_of_locality` (banked) discharges `hbt` ⟹ the unconditional headline.
> - **Status.** sorry-free, axiom-clean (forced `#print axioms`) — awaiting reviewer.
