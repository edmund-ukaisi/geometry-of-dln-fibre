# Statement card — PIN1 (a): the pivot-aligned boundary frame fact

> **Claim.** For a rank-`r` matrix `A : Fin a × Fin b` over `ℝ` whose **tail rows vanish**
> (`A i j = 0` whenever `(i:ℕ) ≥ r`), there is a `B`-determined pivot column set `J : Fin r ↪ Fin b`
> and a **unit** frame `Q : Fin b × Fin b` such that, under the pivot split
> `e := pivotThresholdSplit r b ha J`:
> 1. the lower-right block of `Q` is a unit — `IsUnit ((reindex e e Q).toBlocks₂₂)` (the `B22`
>    invertibility PIN1's reg-slice fderiv needs); AND
> 2. `A·Q` is the block-normal corner in split coordinates —
>    `reindex (rThresholdSplit r a hra) e (A * Q) = fromBlocks 1 0 0 0`.
>
> - **Lean (abstract):** `DLNFibre.DLN.RLCT.exists_pivotFrame_lastBlock_isUnit`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestPivotFrame.lean`, base `71e8694d`).
> - **Lean (deepest-point instance, `2 ≤ L`):** `DLNFibre.DLN.RLCT.exists_deepest_lastLayer_pivotFrame`
>   — the same with `A := deepestPoint H r B hB hr hL (lastLayer hL)` (rank `r` and tail-rows-vanish
>   discharged from `deepestPoint_isDeep`).
>
> - **Gloss / construction (Codex `xhigh` decorrelated design (I)).** Let `V := A.submatrix (Fin.castLE)
>   id` be the top-`r`-rows row factor (`V.rank = r`, proved by `rank_submatrix_le` for `≤` and a
>   zero-padding `range_comp` argument for `≥`). `J := exists_pivot_cols_of_rank V` gives `r` columns of
>   `V` forming a unit. With `VJ`/`VK` the pivot/complement columns of `V` (in `pivotThresholdSplit`'s
>   SORTED order), the explicit split-coordinate frame `Q̃ := fromBlocks VJ⁻¹ (−VJ⁻¹·VK) 0 1` is a unit
>   (block-triangular, `isUnit_fromBlocks_zero₂₁`) with `toBlocks₂₂ = 1`. The actual frame is
>   `Q := reindex e.symm e.symm Q̃` (so `reindex e e Q = Q̃`), and `V·Q = [I_r | 0]` (pivot-aligned),
>   giving the corner via `fromBlocks_multiply` + `mul_nonsing_inv`.
>
> - **Proved (unconditionally).** Both lemmas, zero `sorry`/`axiom`/`native_decide`. Clean-three axioms
>   `{propext, Classical.choice, Quot.sound}` (NO `sorryAx`).
>
> - **Construction CORRECTION (soundness-load-bearing).** The thread-23 brief's route — feed
>   `rank_normal_form_right_only` the column-permuted `A·Pπ` and read `B22` off the generic frame — is
>   **unsound**: `corM` (the right-only normal form) is THRESHOLD-indexed (identity in the FIRST `r`
>   columns), whereas the `B22`-unit needs identity in the chosen PIVOT columns. For non-pivot-front `B`
>   the generic frame's ₂₂-block is **singular** (Codex counterexample `r=1, A=[0 1], A·Q=[1 0]`,
>   pivot col 1, `Q₂₂=0` — exactly the documented obstruction). The banked construction realises
>   `B22 = 1` directly via the explicit `Q̃`, so there is **NO restriction on the rank-`r` `A`** and the
>   keystone `toBlocks22_isUnit_of_pivot_corner` is sidestepped (not needed).
>
> - **Assumed.** rank `r`, tail rows vanish, `r ≤ a`, `r ≤ b`. The deepest-point instance adds the
>   `IsDeepLayers` regime + `2 ≤ L` (for the last-layer tail-rows-vanish clause).
>
> - **Cited.** none (all in-repo + Mathlib v4.29: `exists_pivot_cols_of_rank`, `pivotThresholdSplit`
>   API, `isUnit_submatrix_equiv`, `submatrix_mul_equiv`, `fromBlocks_multiply`, `mul_nonsing_inv`).
>
> - **Status.** sorry-free; awaiting controller wiring into `DLNFibre.lean` + fidelity review.

## Notes — remaining PIN1/PIN2 work (NOT closed this tide)

This card banks frame-fact target **(a)** only. The brief's **(b)** PIN1 body and **(c)** PIN2 cert
remain `sorry` (correctly stated, unchanged) in `DeepestGaugeConstruction.lean`. Both require the
coordinated **`rThresholdSplit → pivotThresholdSplit J` migration** through `deepestEPivot`,
`framedLayer`, `framedParamsReg`, the residual pack, the telescoping, AND the deepest-point frame's
last-layer arm (re-targeted at the banked `Q`) — single-writer-sensitive, several hundred lines, not an
incremental thread-J (the build cannot stay green between the coupled steps). The frame algebra they
stand on is now banked here, and the single shared `J`/`Q` source is `exists_deepest_lastLayer_pivotFrame`.

## Wiring instruction for the controller

Add to `lean/DLNFibre.lean` (single-writer):
`import DLNFibre.DLN.RLCT.Validate.DeepestPivotFrame`
(a new leaf; nothing else imports it yet, so it must be added to the aggregator to enter the green-gate).
