# Statement card — b-FrameM-2 assembly (2): chain-constructor diff atoms, `genm-detcomp`

> **Claim (b-FrameM-2 assembly step 2).** The chaining row `chainQ` and lift column `chainA` are
> `DifferentiableAt` in their matrix arguments — the keystone residual of
> `phiFlatLiveR1_differentiableAt_of_Agen` (`Agen s = chainA(N_s, W_s, Cgen(s+1))`).
>
> - **Lean:** `DLNFibre.DLN.RLCT.{diffAt_chainA, diffAt_chainQ, DifferentiableAt.matMul}`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMChainDiff.lean` @ `<pending — off genm-detcomp 1ae4dd11>`)
> - **Gloss.** `diffAt_chainA`: if `Nf, Wf, Cf` are `DifferentiableAt ℝ … u`, so is `fun x => chainA h
>   (Nf x) (Wf x) (Cf x)`. `diffAt_chainQ`: likewise for `fun x => chainQ h (Nf x)`.
>   `DifferentiableAt.matMul`: the `DifferentiableAt` form of the banked `HasFDerivAt.matMul`.
> - **Proved (unconditional, sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`):** all
>   three, via the PER-ENTRY route.
> - **THE CAST-AVOIDING FINDING (this tide, flag for the record):** `chainQ`/`chainA` are
>   `reindex`/`Sum.elim`/`of` assemblies over a `Fin t ⊕ Fin (M'−t)` SUM-indexed intermediate matrix
>   space, which carries NO norm instance (the banked `instNormedAddCommGroupMatrix`, `RouteMFactorFDeriv`,
>   is for `Fin l`/`Fin m` indices only). So the `reindexLinearEquiv`-as-CLE route STALLS at the
>   Sum-indexed space. The fix: differentiate PER-ENTRY (each entry lands in `ℝ`, always normed) —
>   decompose the row/col index `r : Fin M'` via `finSplit`, then the banked entry laws
>   (`chainA_apply_castAdd`/`_natAdd`, `chainQ_apply_*`) reduce each to `(C−N·W) i j` / `W a j` / `1 i j`
>   / `N i a`. [A decorrelated Codex check on the Sum-indexed-norm dead-end was unavailable (Codex
>   at-capacity); the per-entry workaround was settled empirically. Worth a later Codex pass to confirm
>   there's no cleaner Sum-indexed-norm route.]
> - **Reused (banked, key enabler):** `RouteMFactorFDeriv` — `instNormedAddCommGroupMatrix` (Pi sup-norm
>   on `Matrix (Fin l) (Fin m) ℝ`), `matMulBilin`, `HasFDerivAt.matMul`. (Mirrored, NOT reinvented.)
> - **Assumed.** none.
> - **Cited.** none.
> - **Deferred (the remaining b-FrameM-2 assembly + the ladder):** `Cgen`/`Agen` differentiability
>   (thread `diffAt_chainQ`/`diffAt_chainA` + `.matMul`/`.smul`/`.add` through `Cgen k = Bmat·chainQ +
>   u·Rmat` and `Agen k = chainA(N, W, Cgen(k+1))`) + the decoder-block reads (`genBlkFlatLiveR1`'s
>   `Bmat`/`Nblk`/`Wblk`/`Rmat`/`Rfin` as `DifferentiableAt` in `x` — `bmatStack`/`rmatPad`/reads). Once
>   `Agen` differentiable: `phiFlatLiveR1_differentiableAt_of_Agen` ⟹ `DFrame_M` exists ⟹
>   `toMatrix_blockTriangular_of_locality` discharges `hbt` ⟹ then b-FrameM-1 + b-1 + b-2 ⟹ the
>   unconditional headline.
> - **Status.** sorry-free, axiom-clean (forced `#print axioms`) — awaiting reviewer.
