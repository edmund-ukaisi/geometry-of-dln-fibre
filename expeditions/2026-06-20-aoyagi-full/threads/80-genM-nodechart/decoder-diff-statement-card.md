# Statement card — b-FrameM-2 assembly (3): decoder block-constructor diff atoms, `genm-detcomp`

> **Claim (b-FrameM-2 assembly step 3).** The Schur-frame kept block `bmatStack = [K ; X·K]` and the
> `u`-carrier `rmatPad = [[0,0],[0,E]]` are `DifferentiableAt` in their matrix arguments — the decoder
> block residuals of the per-layer `Cgen`/`Agen` differentiability.
>
> - **Lean:** `DLNFibre.DLN.RLCT.{diffAt_bmatStack, diffAt_rmatPad}` (+ helper entry laws
>   `rmatPad_castAdd_castAdd`, `rmatPad_castAdd_natAdd`)
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMDecoderDiff.lean` @ `<pending — off genm-detcomp 9421f0ac>`)
> - **Gloss.** `diffAt_bmatStack`: if `Kf, Xf` differentiable, so is `fun x => bmatStack M t k hdesc
>   (Kf x) (Xf x)`. `diffAt_rmatPad`: if `Ef` differentiable, so is `fun x => rmatPad M t s h1 h2 (Ef x)`.
> - **Proved (unconditional, sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`; the two
>   `rmatPad` zero-laws `[propext, Quot.sound]`):** all four, via the per-entry route.
> - **New helper laws:** `rmatPad_castAdd_castAdd` / `rmatPad_castAdd_natAdd` — the two missing TOP-row
>   (`= 0`) entry laws of `rmatPad` (the codebase had only the bottom-row `_natAdd_*`); derived here for
>   the full 4-way `fromBlocks` per-entry case split.
> - **CAST FINDING (this tide):** the `inr b` (`X·K`) case of `diffAt_bmatStack` hit a `whnf` TIMEOUT
>   matching the matMul-entry `(X·K) b j` against `DifferentiableAt.matMul`'s output. Fix: rewrite the
>   entry to its EXPLICIT SUM form (`Matrix.mul_apply`) first, then `DifferentiableAt.fun_sum` + `.mul`
>   per term — avoiding the matMul whnf. (Same Pi-form / per-entry / explicit-sum lesson; the matMul-CLM
>   form whnf-stalls where the explicit sum does not. [Codex at-capacity — settled empirically.])
> - **Assumed.** none.
> - **Cited.** none.
> - **Deferred (the remaining b-FrameM-2 assembly):** (i) `Cgen` differentiability (thread `diffAt_chainQ`
>   + `.matMul`/`.smul`/`.add` + `diffAt_bmatStack`/`diffAt_rmatPad` + the decoder reads through `Cgen k =
>   Bmat·chainQ(Nblk) + u·Rmat`, interior/leaf `dif` split); (ii) the decoder READS (`readK/X/N/E/W` as
>   `DifferentiableAt` in `x` — single-coordinate reads through `chartIdxEquiv.symm`) + the `Function.update`
>   fixed-pivot override + `rfin x` leaf; (iii) `Agen = chainA(Nblk, Wblk, Cgen(k+1))` assembling all via
>   `diffAt_chainA`. Then `phiFlatLiveR1_differentiableAt_of_Agen` ⟹ `DFrame_M` exists ⟹
>   `toMatrix_blockTriangular_of_locality` discharges `hbt` ⟹ b-FrameM-1 + b-1 + b-2 ⟹ unconditional headline.
> - **Status.** sorry-free, axiom-clean (forced `#print axioms`) — awaiting reviewer.
