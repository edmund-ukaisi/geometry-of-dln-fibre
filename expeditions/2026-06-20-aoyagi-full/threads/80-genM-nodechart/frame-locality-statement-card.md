# Statement card — b-FrameM-3 keystone (value-locality ⟹ fderiv block-triangular), `genm-detcomp`

> **Claim (b-FrameM-3, the RISK piece de-risked).** The PROVEN value-level off-block-vanishing
> (`Agen_genBlkFlatStruct_reads_le`: output layer `s` reads only input layers `≤ s`) lifts to the
> **fderiv-level** off-block-vanishing — i.e. the chart's Jacobian matrix `toMatrix' DFrame_M` is
> block-triangular under the layer grading. The calculus fact: a function whose `i`-th output coord is
> invariant under changing input coord `j` has `∂(output i)/∂(input j) = 0`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.toMatrix_blockTriangular_of_locality` +
>   `DLNFibre.DLN.RLCT.fderiv_apply_single_proj_zero_of_indep`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMFrameLocality.lean` @ `<pending — off genm-detcomp 9ac2a975>`)
> - **Gloss.** For `f : (Fin N → ℝ) → (Fin N → ℝ)` with `HasFDerivAt f D u`:
>   - `fderiv_apply_single_proj_zero_of_indep`: if `f`'s `i`-th output coord is invariant under changing
>     input coord `j` (`f v i = f u i` whenever `v` agrees with `u` off `j`), then `(D eⱼ) i = 0`.
>   - `toMatrix_blockTriangular_of_locality`: if for every `i, j` with `g i < g j` the `i`-th output is
>     invariant under input `j`, then `toMatrix' D` is `BlockTriangular (OrderDual.toDual ∘ g)` (entry
>     `(i,j)` vanishes when `g j > g i` — the LOWER-triangular form the verdict names).
> - **Proved (unconditional, sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`):** both
>   lemmas, network-free (Mathlib calculus + matrix only). The directional-derivative-of-a-constant-line
>   argument; no entrywise `DFrame_M` computation. In-file non-vacuity: both fire on a constant map.
> - **Assumed.** none (the lemmas are unconditional; the value-level locality `hloc` is supplied by the
>   caller — banked `Agen_genBlkFlatStruct_reads_le` once lifted through the reshape).
> - **Cited.** none.
> - **Deferred (the remaining b-FrameM ladder, named — the honest ceiling of this tide):**
>   - **b-FrameM-2 (the long pole):** `HasFDerivAt phiFlatLiveR1 D u` over OPAQUE `Fin (Wext M k)` widths.
>     Empirically confirmed (this tide) that `fun_prop` does NOT discharge it — `Matrix.of` has no
>     `fun_prop` theorems and `Matrix.mul` over opaque widths times out at `whnf`. The chart is a
>     polynomial map (finite matrix products + a linear reshape), so it IS differentiable, but the Lean
>     proof needs MANUAL compositional `HasFDerivAt` via the bilinear `Matrix.mul` derivative + the
>     dependent-width cast handling (the cast-thrash zone). Genuine multi-tide piece.
>   - **b-FrameM-1:** `Frame_M`/`Q_M` defs + `|det Q_M| = 1` (generalize `Q3333CLM_abs_det` via the
>     banked `paramsEquivFlatCLE`) + `paramsPack_layer` (reshape preserves `bLayer`).
>   - **b-1:** the opaque-width `toSquareBlock` reindex (`card_equiv`), feeding the banked b-3 headline.
>   Once b-FrameM-2 lands, `toMatrix_blockTriangular_of_locality` discharges `hbt` directly (`f :=
>   phiFlatLiveR1`, `g := bLayer`, `hloc :=` lifted `Agen_genBlkFlatStruct_reads_le`).
> - **Status.** sorry-free, axiom-clean (forced `#print axioms`) — awaiting reviewer.
