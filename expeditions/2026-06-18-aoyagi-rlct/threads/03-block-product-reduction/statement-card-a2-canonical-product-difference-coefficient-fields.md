# Statement Card - A2 Canonical Product-Difference Coefficient Fields

> **Claim.** A deterministic suffix-state block-diagonalization gives the
> product-difference entry-ideal equality with canonical coefficient fields
> `F2 = -S.B`, `F3 = lowerLeftBlock S.L`, `Ctop = S.Ctop`, and `D = S.D`,
> rather than existential off-diagonal witnesses.
>
> - **Source anchor:** Aoyagi 2023 preprint, p. 13, after Theorem 3.
> - **Lean target:** `ChartLocalSuffixState.productDifferenceEntryIdeal_eq_fourMatrixEntryIdeal`
>   and the fixed-base endpoint corollary in
>   `lean/DLNFibre/DLN/Aoyagi/ProductReductionEntryIdealBoundary.lean`.
> - **Gloss.** The suffix-state invariant already supplies
>   `S.L * P * [I -S.B; 0 I] = [S.Ctop 0; 0 S.D]`.  Since `S.L` is lower
>   unitriangular, it equals `[I 0; lowerLeftBlock S.L I]`; applying the
>   existing p. 13 entry-ideal cleanup gives the four deterministic generator
>   families.
> - **Pen-and-paper check:**
>   `reproduction-a2-canonical-product-difference-coefficient-fields.md`.
> - **Proved:** Rank-free algebraic scalar entry-ideal equality for a
>   deterministic suffix state, plus the fixed-base endpoint specialization
>   from the existing product-reduction certificate.
> - **Assumed:** A supplied/proved suffix-state block-diagonal invariant.  In
>   the fixed-base specialization this is exactly the existing certificate
>   field.
> - **Cited:** None.
> - **Deferred:** Exact-rank openness, source-rank neighborhood construction,
>   analytic germ-ideal transport, analytic regularity, chart coverage, normal
>   crossings, pole order, and RLCT.
> - **Kill conditions:** Do not read the theorem as an analytic ideal theorem.
>   Do not replace `S.D` by a raw lower-right edge product without a separate
>   transformed-residual product theorem.
