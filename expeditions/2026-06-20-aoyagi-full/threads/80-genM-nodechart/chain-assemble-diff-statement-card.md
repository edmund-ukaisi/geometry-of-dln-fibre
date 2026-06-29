# Statement card — b-FrameM-2 COMPLETE: DifferentiableAt phiFlatLiveR1, `genm-detcomp`

> **Claim (b-FrameM-2 done).** The R1 active-center chart `phiFlatLiveR1` is `DifferentiableAt` over
> OPAQUE width tuples (given the live leaf `rfin` differentiable) — i.e. its Jacobian `DFrame_M` EXISTS.
> This is the existence the b-FrameM-3 keystone (`toMatrix_blockTriangular_of_locality`) consumes to
> discharge the interior-det headline's `hbt`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.phiFlatLiveR1_differentiableAt`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMChainAssembleDiff.lean` @ `<pending — off genm-detcomp 6b536207>`)
>   Supporting: `diffAt_read{K,X,N,E,W}`, `diffAt_live{Bmat,Nblk,Wblk,Rmat,Rfin}`, `diffAt_Cgen`,
>   `diffAt_Agen`.
> - **Gloss.** For `hN : 0 < routeMAmbient M`, `u`, and `hrfin : DifferentiableAt ℝ rfin u`:
>   `DifferentiableAt ℝ (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin) u`. Threads the banked atoms
>   (`chainQ`/`chainA`/`matMul`/`bmatStack`/`rmatPad`) through the live decoder's 5 blocks → `Cgen` →
>   `Agen` → `phiFlatLiveR1_differentiableAt_of_Agen` (the top reduction).
> - **Proved (unconditional, sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`):** the
>   full chain, every layer.
> - **Cast-management used (all empirical; Codex at-capacity):** Pi form (not abstract Matrix); matMul
>   ENTRIES → explicit-sum (the CLM whnf-stalls); the live `Rmat`'s `Function.update` over a DEPENDENT
>   matrix codomain → `split_ifs` INSIDE the diff goal (no index rewrite — sidesteps "motive not type
>   correct", per the coordinator's hint); `Rfin`'s `dite (k = L)` → `by_cases` + `subst`.
> - **Assumed.** `hrfin : DifferentiableAt ℝ rfin u` — the live leaf `rfin` (the budget-rerouted leaf
>   block reader) is differentiable. This is satisfied when `rfin` is itself a coordinate-read assembly
>   (the budget piece); it is the one carried hypothesis, the same shape as the decoder reads.
> - **Cited.** none (Mathlib calculus + the banked matrix fderiv `RouteMFactorFDeriv`).
> - **Deferred (the final connect + the ladder):** discharge `hbt` by feeding
>   `phiFlatLiveR1_differentiableAt` (the `DFrame_M = fderiv` existence) +
>   `toMatrix_blockTriangular_of_locality` (b-FrameM-3, banked) + the value-level locality
>   `Agen_genBlkFlatStruct_reads_le` (lifted to the live decoder + transported through `bLayer`). Then
>   `interiorDet_headline_of_blockTri` (b-3) ⟹ the headline, modulo b-FrameM-1 (`Frame_M`/`Q_M` +
>   `|det Q_M| = 1`) + b-1 (`toSquareBlock` reindex) + b-2 (per-layer diagonal det = engine value).
> - **Status.** sorry-free, axiom-clean (forced `#print axioms`) — awaiting reviewer.
