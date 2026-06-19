# Statement card - A2 unitriangular chart stability

> **Claim.** If a true next-layer block has identity top-left corner and zero
> lower-left block, then multiplying on the left by an upper unitriangular block
> matrix preserves the identity top-left corner and zero lower-left block.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.upperUnitriangular_mul_fromBlocks_one_zero`
>   (`lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean` @ `f701115`)
> - **Gloss.** Over a commutative ring,
>   `fromBlocks 1 (-F) 0 1 * fromBlocks 1 B 0 D =
>   fromBlocks 1 (B - F * D) 0 D`. This is the local block calculation used in
>   the through-layer basis/open-chart repair.
> - **Proved.** The purely algebraic block identity, including the sign and the
>   updated upper-right block `B - F * D`.
> - **Assumed.** Matrix dimensions encoded by `Fin` indices. No determinant,
>   rank, or analytic hypotheses are used.
> - **Cited.** None.
> - **Deferred.** The field-linear through-subspace existence theorem; the
>   matrix basis-change corollary; full Aoyagi Theorem 3; local analytic
>   coordinate invariance; normal-crossing certificate transport; and every
>   RLCT or pole-order consequence.
> - **Status.** sorry-free, axiom-clean scanner clean, targeted and full
>   `DLNFibre` builds pass; xhigh checker `Hooke` accepted the surrounding
>   through-layer reproduction and this local chart-stability calculation as
>   formalisation-ready.
