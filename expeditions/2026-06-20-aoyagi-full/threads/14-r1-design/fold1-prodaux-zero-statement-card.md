# Statement card — #123 FOLD1: the idempotent `prodAux`-at-0 fold + `deepestEPivot_base`

> **Claim.** At the origin gauge slot, the framed (T=0) layer product `∏(framedParamsReg 0)` is the
> reindexed block-normal corner `blockdiag[I_r, 0]`, and hence the regular pivot residual
> `deepestEPivot 0 = 0`. This is FOLD1 (value) of the #123 `prodAux` fold family — the cast-wall break
> that gated `deepestEPivot_base`.
>
> - **Lean:**
>   - `DLNFibre.DLN.RLCT.prodAux_framedParamsReg_zero_aux` and
>     `DLNFibre.DLN.RLCT.prodAux_framedParamsReg_zero` (crux2's single-writer
>     `lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean`, authoritative @ `4052a28`).
>   - `DLNFibre.DLN.RLCT.deepestEPivot_base`
>     (`lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean` @ `4052a28`).
>
> - **Gloss.** Every layer of `framedParamsReg H r hr hL 0` is, at the origin, the block-normal corner
>   `reindex (rThresholdSplit …).symm (rThresholdSplit …).symm (fromBlocks 1 0 0 0)`
>   (`framedParamsReg_zero`). The corner is idempotent under the chain product, so the running product
>   through `k ≥ 1` layers is again the corner at width `H 0 × H ⟨k⟩` (`prodAux_framedParamsReg_zero_aux`),
>   and at `k = L` this is `∏ = reindex(corner)` (`prodAux_framedParamsReg_zero`). The pivot residual
>   `deepestEPivot p` reads the `(P11−I, P12, P21)` blocks of `reindex(∏)` — for `p = 0`, the outer
>   reindex cancels the corner's reindex (`reindex e f (reindex e.symm f.symm corner) = corner`), so the
>   blocks are exactly `(I−I, 0, 0) = 0`.
>
> - **The cast break (the named #123 gate).** The `prodAux` succ-step carries a dependent-`Fin` cast:
>   the running index `H ⟨k, hk'⟩` vs the layer's stated index `H ⟨k, hkL⟩.castSucc` are DEFINITIONALLY
>   equal (`Fin` proof-irrelevance + `castSucc ⟨k,_⟩` reduction = `rfl`) but NOT syntactic, blocking the
>   matrix-VALUE rewrite of `framedParamsReg_zero` under the fold. TWO independent cracks:
>   - **cobuild:** after `rw [prodAux_succ … e1 e2]` the layer is
>     `reindex (finCongr e1.symm) (finCongr e2.symm) (…)`; since `e1, e2 : rfl`, `finCongr_refl` rewrites
>     `finCongr e1.symm = Equiv.refl`, and the whole layer-collapse closes by `rfl`
>     (`reindex (refl) (refl) M` reduces definitionally). Then `rcases` on `k`: `k = 0` → `Matrix.one_mul`
>     (the `prodAux 0 = 1` head), `k ≥ 1` → `rw [ih]` + `corner_reindex_mul` (the idempotent
>     `corner · corner = corner`).
>   - **crux2:** `prodAux_succ_layer` — the SHARED step-cast kernel; the index-level `cases e1; cases e2`
>     collapses the def's `Eq.mpr`/cast (the `contDiff_prodAux_entry` precedent). The reusable family piece.
>
> - **Proved (sorry-free; clean-three `[propext, Classical.choice, Quot.sound]`).**
>   `prodAux_framedParamsReg_zero_aux`, `prodAux_framedParamsReg_zero`, `deepestEPivot_base` — all
>   verified `#print axioms`.
>
> - **Building blocks (crux2, axiom-clean):** `prodAux_succ` (explicit `e1/e2` + `Subsingleton.elim`),
>   `prodAux_succ_layer` (the kernel), `corner_reindex_mul` (`submatrix_mul_equiv` + `fromBlocks_multiply`).
>
> - **NOT this card.** The OTHER two folds remain (their own PINs, NOT FOLD1):
>   - `deepestEPivot_deriv` (#82): the `HasStrictFDerivAt` Leibniz derivative + shear — analytic, OPEN.
>   - `deepest_loss_squeeze` (#80): the two-sided Frobenius bound — geometric identification, OPEN.
>   - `endpoint_telescoping` (crux2's lane): the stronger exact equality `∏C = P0·∏A·QL`, OFF the L2
>     critical path (verdict-a).
