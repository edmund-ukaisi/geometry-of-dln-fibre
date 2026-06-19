# Statement card - A2 unitriangular chart stability

> **Claim.** If a true next-layer block has identity top-left corner and zero
> lower-left block, then multiplying on the left by an upper unitriangular block
> matrix preserves the identity top-left corner and zero lower-left block.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.upperUnitriangular_mul_fromBlocks_one_zero`
>   and
>   `DLNFibre.DLN.Aoyagi.exists_fromBlocks_one_zero_of_upperUnitriangular_mul`
>   and their indexed variants
>   `upperUnitriangular_mul_fromBlocks_one_zero_indexed`,
>   `exists_fromBlocks_one_zero_of_upperUnitriangular_mul_indexed`
>   (`lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`).
> - **Gloss.** Over a commutative ring,
>   `fromBlocks 1 (-F) 0 1 * fromBlocks 1 B 0 D =
>   fromBlocks 1 (B - F * D) 0 D`. This is the local block calculation used in
>   the through-layer basis/open-chart repair. The existential corollary says
>   any matrix known to have some form `fromBlocks 1 B 0 D` remains in some
>   form `fromBlocks 1 B' 0 D'` after this upper-unitriangular multiplication.
>   The indexed versions allow arbitrary finite row/inner index types, matching
>   the basis indices used by the through-layer chart data.
> - **Proved.** The purely algebraic block identity, including the sign and the
>   updated upper-right block `B - F * D`, plus the chart-form preservation
>   corollary.
> - **Assumed.** Matrix dimensions encoded by `Fin` indices. No determinant,
>   rank, or analytic hypotheses are used.
> - **Cited.** None.
> - **Deferred.** Bundling the per-edge through-basis/complement data into the
>   full product-reduction induction; full Aoyagi Theorem 3; local analytic
>   coordinate invariance; normal-crossing certificate transport; and every
>   RLCT or pole-order consequence.
> - **Status.** sorry-free, axiom-clean scanner clean, targeted and full
>   `DLNFibre` builds pass; xhigh checker `Hooke` accepted the surrounding
>   through-layer reproduction and this local chart-stability calculation as
>   formalisation-ready.
