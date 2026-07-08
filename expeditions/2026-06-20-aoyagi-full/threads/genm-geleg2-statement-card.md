# Statement card — general-`L` block-layer-product ↔ DLN `prod` bridge (piece ii of D1 ≥-leg chart data)

> **Claim.** For any injective per-vertex pivot family `ι : (s : Fin (L+1)) → Fin r → Fin (H s)` and
> any `v : Params H`, the DLN prefix product `prodAux H v k` reindexed by the common-pivot splits
> `sumSplit (ι ·)` equals the cast-free `partProd` fold of the block chain `genChain`, and its `(1,1)`
> block is the prefix-product pivot minor. (General-`L`, general-pivot lift of `blockFlatEquiv_L2_mul`.)
>
> - **Lean:** `DLNFibre.DLN.RLCT.reindex_prodAux_eq_genPartProd`,
>   `reindex_prod_eq_genPartProd`, `genPartProd_toBlocks₁₁`
>   (`lean/DLNFibre/DLN/RLCT/Validate/D1GeBlockProd.lean` @ `88e5d70b`)
> - **Gloss.**
>   - `genChain … v` is the `ℕ`-indexed block chain: layer `s` is the DLN layer `v s` recast to the
>     running widths (`deepestChainLayer`, pivot-independent) and reindexed into `r ⊕ (dcw s − r)`
>     block shape by `sumSplit (genPivotN s)` at both vertices (`genPivotN` = `ι` on `s ≤ L`, a first-`r`
>     `Fin.castLE` past the last layer — never read by `partProd … L`, present only for totality).
>   - `reindex_prodAux_eq_genPartProd`: for all `k ≤ L`,
>     `reindex (sumSplit (ι 0)).symm (genChainCol k) (prodAux H v k) = partProd (genChain …) k`.
>   - `reindex_prod_eq_genPartProd`: the `k = L` case on the full product `prod H v`.
>   - `genPartProd_toBlocks₁₁`: `(partProd (genChain …) k).toBlocks₁₁
>     = (prodAux H v k).submatrix (ι 0) (ι ⟨k, hk⟩)` — the block corner is exactly the prefix-product
>     minor `exists_common_pivot_gen` (piece i) makes invertible.
> - **Proved.** All three, unconditionally, sorry-free, over `ℝ`. Axiom footprint (forced
>   `#print axioms`, all three): `[propext, Classical.choice, Quot.sound]` — no `sorryAx`. `r = 0`
>   and the tail (`s > L`) handled.
> - **Assumed.** `hι : ∀ s, Injective (ι s)` (injectivity of the pivot family) and `hr : ∀ s, r ≤ H s`
>   (the running-width bound, for the `ℕ`-extension). NOT the pivot-minor invertibility — the bridge
>   is a pure reindex identity for any injective `ι`; invertibility is piece (i), applied downstream.
> - **Cited.** none. Reuses banked Core/sibling API: `deepestChainWidth` (+ `_castSucc`, `_succ`,
>   `H_eq_deepestChainWidth`, `r_le_deepestChainWidth`), `deepestChainLayer`, `reindex_mul_split_gen`
>   (all `DeepestFinBridgeGen`, pivot-independent), `partProd` (`DeepestSchurRecursion`), `sumSplit`
>   (`D1L2PhiExpl`), `prodAux_succ` (`Foundations.Loss`), `Matrix.submatrix_one_equiv`.
> - **Deferred.** none for this bridge. (Downstream: turning `genPartProd_toBlocks₁₁` + piece (i) into
>   `IsUnit (partProd …).toBlocks₁₁` and running the Schur telescope is pieces iii/iv.)
> - **Structure & ideas observed.** Exact mirror of the achiever-side `reindex_prodAux_eq_partProd`
>   with the first-`r` threshold split swapped for `sumSplit (ι ·)`; the achiever's cast-free width
>   bookkeeping and shared-middle cancel transfer verbatim. Two cast subtleties, both isolated: (a) the
>   succ-step `reindex_mul_split_gen` rewrite requires the row equiv to have domain **syntactic**
>   `Fin (H 0)` (hence `(sumSplit (ι 0)).symm`, not `genChainCol 0`), matching `prodAux`'s row; (b) the
>   `genPartProd_toBlocks₁₁` column reduces via `sumSplit_inl` + the `genPivotN` `finCongr` recast
>   cancelling its inverse (`Fin.cast_cast`/`Fin.cast_eq_self`).
> - **Route.** Achiever-mirror with `sumSplit (ι ·)` (this thread).
> - **Status.** sorry-free + reviewed (reviewer verdict OVERALL PASS: fidelity of all three theorems,
>   the `toBlocks₁₁` corner = piece (i)'s minor with no transpose, non-vacuity, weakest-hypotheses, and
>   proof soundness all PASS; forced-olean-deletion `#print axioms` re-verified clean three. Confirmed
>   the `gen*`-vs-`deepest*` duplication is justified — `sumSplit`'s complement ordering differs from
>   `rThresholdSplit`'s `natAdd`, so no unification. Nit applied: import `D1GeBlockModel` → `D1L2PhiExpl`
>   (only `sumSplit`/`sumSplit_inl` used), lighter closure, @ `7f23f971`.)
