**Q1**

Cheapest route: build the selector lemma once, using column span, then repeat on rows.

1. Rewrite rank by columns:
   `Matrix.rank_eq_finrank_span_cols`.

2. Extract a basis-sized independent subfamily from the actual column set:
   `Submodule.exists_fun_fin_finrank_span_eq k (Set.range A.col)`.
   After rewriting `finrank ... = r`, choose witnesses `t : Fin r → Fin q` from membership in `Set.range A.col`. Use `LinearIndependent.injective` to prove `Function.Injective t`.

3. For `C := A.submatrix id t`, identify its columns with the chosen family using:
   `Matrix.col_submatrix_eq_comp`.
   Then prove `C.rank = r` by applying `LinearIndependent.rank_matrix` to `Cᵀ`, plus:
   `Matrix.rank_transpose`.

4. Repeat on rows of `C`, using:
   `Matrix.rank_eq_finrank_span_row`,
   `Submodule.exists_fun_fin_finrank_span_eq k (Set.range C.row)`.
   Choose row witnesses `s : Fin r → Fin p`; injectivity again comes from `LinearIndependent.injective`.

5. For `D := A.submatrix s t`, use:
   `Matrix.submatrix_submatrix`,
   `Matrix.row_submatrix_eq_comp`,
   `Matrix.linearIndependent_rows_iff_isUnit`,
   `Matrix.isUnit_iff_isUnit_det`.

There is no verified existing Mathlib lemma of the form “rank `r` gives an invertible `r × r` minor”. Estimate: 180-260 LoC if polished with helper lemmas. Hardest step: proving the selected-column matrix has rank exactly `r`, mostly because of casts through `Fin (finrank ...)` and identifying columns after `submatrix`.

**Q2**

Use reindexing, not a direct arbitrary-Schur restatement. Public pivot positions should be unordered subsets:

1. Define the index type as:
   `Set.powersetCard (Fin p) r × Set.powersetCard (Fin q) r`
   or equivalently `{S : Finset (Fin p) // S.card = r}` pairs. Prefer `Set.powersetCard`: it already has `Set.powersetCard.orderIsoOfFin`.

2. For `S : Set.powersetCard (Fin p) r`, build the row equivalence
   `Fin r ⊕ Fin (p - r) ≃ Fin p`
   from:
   `Set.powersetCard.orderIsoOfFin`,
   `Finset.card_compl`,
   `Equiv.sumCongr`,
   `Equiv.Set.sumCompl`.
   Same for columns.

3. Define the chart by reindexing:
   `M ∈ chart S T` iff
   `M.submatrix rowEquiv colEquiv ∈ pivotRankChart k (Fin r) (Fin (p-r)) (Fin (q-r))`.

4. Reuse the landed equivalence literally:
   reindex-subtype equivalence, then `pivotRankChartEquiv`.
   Rank preservation uses `Matrix.rank_submatrix`; block/top-left identification is by unfolding `Matrix.toBlocks₁₁` and `Matrix.submatrix_apply`.

5. For the cover, Q1 gives arbitrary injective `s,t`; convert to finsets via `Finset.image` and `Finset.card_image_of_injective`. To compare the arbitrary minor with the sorted `orderEmbOfFin` minor, use determinant permutation lemmas:
   `Matrix.det_permute`,
   `Matrix.det_permute'`.
   The sign is a unit via `IsUnit.mul`/unit coercions.

Estimate: 150-230 LoC for B3-1 chart family and equivalence, plus 40-80 LoC to connect Q1’s arbitrary selectors to sorted finset-indexed minors. Hardest step: determinant invariance under changing from arbitrary injective selectors to the canonical sorted `Finset.orderEmbOfFin` selectors.

**Q3**

Ship B3-2+B3-1, disclaim B3-3.

Base-change homogeneity does not give transitions for free. It gives existential `GL × GL` transport between rank-equal matrices/fibres, but not canonical regular maps on overlaps, not formulas in localized coordinate rings, and not cocycle/coherence data. At best it says the local models are abstractly equivalent after choosing base changes; it does not compare the two localization `AlgEquiv`s induced by different pivot minors.

A useful one-tide deliverable is: fully proved rank-minor cover plus matrix-level per-minor charts with `GL_r × Mat × Mat` bijections. Treat transition coherence and localized `AlgEquiv` comparison as the next rung.