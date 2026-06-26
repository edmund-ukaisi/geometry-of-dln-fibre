# Statement card — per-minor open cover of `Mat^{=r}` + chart family (B3-1, B3-2)

Thread 18 (`18-perminor-bundle`). Builds the genuine per-minor-position open cover that thread-11
(`FibreBundleReduced`) explicitly disclaimed (it had only the single top-left chart `e_β`).

---

## Card 1 — the rank ↔ minor bridge (B3-2 keystone)

> **Claim.** Over a field, a matrix of rank `r` has **some** invertible `r × r` minor: there are
> injective row/column selectors `s, t` with the `(s, t)` submatrix invertible. (The determinantal-rank
> existence fact — **not** in Mathlib v4.29.)
>
> - **Lean:** `DLNFibre.Core.exists_invertible_minor_of_rank`
>   (`lean/DLNFibre/Core/RankMinorCover.lean` @ `67dff40b`)
> - **Gloss.** For `A : Matrix (Fin p) (Fin q) k` (`k` a field) with `A.rank = r`, there exist
>   `s : Fin r → Fin p` and `t : Fin r → Fin q`, both `Function.Injective`, with
>   `IsUnit ((A.submatrix s t).det)`.
> - **Proved.** Unconditionally (any field). Route: `rank = finrank (span cols)`
>   (`Matrix.rank_eq_finrank_span_cols`); `Submodule.exists_fun_fin_finrank_span_eq` pulls `r`
>   independent columns by index (`exists_injective_cols_linearIndependent`); the `p × r` column
>   restriction has rank `r`, and a second index-extraction on its transpose +
>   `Matrix.linearIndependent_rows_iff_isUnit` gives the invertible square minor
>   (`exists_invertible_square_minor_of_cols_linearIndependent`).
> - **Assumed.** `[Field k]` only.
> - **Cited.** none.
> - **Deferred.** none.
> - **Status.** sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]`.

## Card 2 — the per-minor opens cover `Mat^{=r}` (B3-2 headline)

> **Claim.** The det-open family `{minorChart s t}` over the pivot positions `(s, t)` is a genuine
> open cover of the rank-exactly-`r` locus `Mat^{=r}`.
>
> - **Lean:** `DLNFibre.Core.rankEqLocus_subset_iUnion_minorChart` and
>   `DLNFibre.Core.rankEqLocus_eq_iUnion_inter_minorChart`
>   (`lean/DLNFibre/Core/RankMinorCover.lean` @ `67dff40b`)
> - **Gloss.** `minorChart k p q s t := {M | IsUnit ((M.submatrix s t).det)}` (the principal
>   det-open where the `(s, t)` minor is invertible), `rankEqLocus r := {M | M.rank = r}`. Then
>   `rankEqLocus r ⊆ ⋃ (st : (Fin r → Fin p) × (Fin r → Fin q)), minorChart k p q st.1 st.2`, and
>   the refined equality `rankEqLocus r = ⋃ st, (rankEqLocus r ∩ minorChart k p q st.1 st.2)`.
> - **Proved.** Unconditionally; every rank-`r` matrix lies in some chart (Card 1).
> - **Assumed.** `[Field k]`.
> - **Cited.** none. **Deferred.** none.
> - **Status.** sorry-free; axiom-clean.

## Card 3 — per-minor chart = top-left chart of a permuted matrix (B3-1)

> **Claim.** Each per-minor pivot chart reduces, by a coordinate permutation, to the **single** built
> top-left pivot chart `Core.pivotRankChart`; hence it inherits the explicit `GL_r × Mat × Mat` Schur
> parametrization.
>
> - **Lean:** `DLNFibre.Core.mem_minorChart_inter_rankEqLocus_iff` and
>   `DLNFibre.Core.minorChartEquiv`
>   (`lean/DLNFibre/Core/FibreBundlePerMinor.lean` @ `67dff40b`)
> - **Gloss.** `perMinorEquiv s hs : Fin r ⊕ ↥(range s)ᶜ ≃ Fin p` puts the selected rows first
>   (`Equiv.ofInjective` + `Equiv.Set.sumCompl`); `reindex` by it carries the `(s, t)` minor to the
>   top-left block (`submatrix_eq_toBlocks₁₁_reindex`) and preserves rank (`Matrix.rank_reindex`). So
>   `M ∈ rankEqLocus r ∧ M ∈ minorChart s t ↔ (reindexed M) ∈ pivotRankChart` (membership-iff), and
>   `minorChartEquiv` is the resulting bijection of the per-minor chart subtype with
>   `{Δ // IsUnit Δ.det} × Matrix (Fin r) ↥(range t)ᶜ k × Matrix ↥(range s)ᶜ (Fin r) k` (transport of
>   `Core.pivotRankChartEquiv`).
> - **Proved.** Each per-minor chart is the top-left chart of a permuted matrix, with the
>   `GL_r × Mat × Mat` parametrization. `minorChartEquiv` / the `pivotRankChart` reuse pin the field to
>   `Type` (universe 0) — harmless (the DLN application is `k = ℂ`).
> - **Assumed.** `[Field k]`; `Type`-monomorphic for the `pivotRankChart` reuse (Card-3 only).
> - **Cited.** none.
> - **Deferred (B3-3, NOT built).** The **transition coherence**: the comparison of the two
>   **localized coordinate-ring `AlgEquiv`s** `e_{S,T} ∘ e_{S',T'}⁻¹` on chart overlaps. This requires
>   comparing two ~250-LoC localization equivalences and is the next rung. Base-change homogeneity
>   (`Core.FibreNormalForm`) gives only existential `GL × GL` transport, **not** the cocycle data, so it
>   does **not** discharge B3-3 for free (Codex-confirmed). Accordingly the package is **not** named
>   `locallyTrivial`.
> - **Route (controller-synthesized, Codex-vetted).** Column-span index-extraction for the bridge
>   (`exists_fun_fin_finrank_span_eq`, twice, glued by transpose); `Equiv.ofInjective`/`Set.sumCompl`
>   reindex for the per-minor chart. Decorrelated local-codex-consult (xhigh) confirmed both routes and
>   the scope call ("ship B3-2+B3-1, disclaim B3-3"):
>   `threads/18-perminor-bundle/codex/perminor-route-{prompt,answer}.md`.
> - **Status.** sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]`.

---

## Aggregator import lines (controller to wire — single-writer `DLNFibre.lean`)

```
import DLNFibre.Core.RankMinorCover
import DLNFibre.Core.FibreBundlePerMinor
```

(`FibreBundlePerMinor` imports `RankMinorCover` and `DeterminantalChart`; `RankMinorCover` is
network-free / Mathlib-adjacent — a spin-out candidate, like `mvPolynomialAwayMapTensorAlgEquiv`.)
