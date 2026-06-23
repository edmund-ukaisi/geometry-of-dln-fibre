# Statement card - A2 block product-difference algebra

> **Claim.** If Aoyagi's triangular endpoint multipliers put a block matrix
> `T` into endpoint block-diagonal form, then subtracting the rank-model block
> `T0 = fromBlocks 1 0 0 0` gives the displayed product-difference block
> matrix
>
> ```text
> L(F3) * (T - T0) * R(F2)
>   = fromBlocks (Ctop - 1) (-F2) (-F3) (D - F3 * F2).
> ```
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.triangularBlockProductDifference_fromBlocks_indexed`
>   in `lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`.
> - **Gloss.** Here
>   `L(F3) = fromBlocks 1 0 F3 1`,
>   `R(F2) = fromBlocks 1 F2 0 1`, and
>   `T0 = fromBlocks 1 0 0 0`.  The theorem assumes
>   `L(F3) * T * R(F2) = fromBlocks Ctop 0 0 D` and proves the displayed
>   difference identity by distributivity and direct block multiplication.
> - **Proved.** The signs and lower-right correction are fixed by block
>   subtraction: the lower-right block is `D - F3 * F2`.
> - **Assumed.** Finite block indices, decidable equality on square identity
>   blocks, a commutative base ring, and the endpoint triangular block form.
> - **Cited.** None.
> - **Deferred.** Source production of the endpoint triangular block form, full
>   Aoyagi Theorem 3 from rank/neighborhood hypotheses, Aoyagi Lemma 1,
>   analytic generator transport, regular-suspension normal-crossing
>   construction, pole order, and RLCT.
> - **Status.** Focused build
>   `cd lean && scripts/lb DLNFibre.DLN.Aoyagi.ProductReduction` passes.
>   Independent pen-and-paper check by `Lorentz` agrees with the signs and
>   dimensions.  Xhigh fidelity/scope review by `Fermat` passed with no fixes.
