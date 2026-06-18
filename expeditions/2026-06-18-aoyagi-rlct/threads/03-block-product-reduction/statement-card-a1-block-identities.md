# Statement card - A1 block-elimination identities

> **Claim.** On the chart where the top-left block `A1` has unit determinant,
> Aoyagi's triangular block multiplications transform
> `fromBlocks A1 A2 A3 A4` first to its Schur-complement form and then to a
> block-diagonal matrix with lower-right block `A4 - A3 * A1⁻¹ * A2`.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.schurComplement_leftBlockElim_fromBlocks` and
>   `DLNFibre.DLN.Aoyagi.schurComplement_blockElim_fromBlocks`
>   (`lean/DLNFibre/DLN/Aoyagi/BlockElimination.lean` @ `cd3a4e0`)
> - **Gloss.** For matrices over a commutative ring, assuming
>   `hA1 : IsUnit A1.det`, left multiplication by
>   `fromBlocks 1 0 (-(A3 * A1⁻¹)) 1` replaces the lower-right block by the
>   Schur complement and zeros the lower-left block; subsequent right
>   multiplication by `fromBlocks 1 (-(A1⁻¹ * A2)) 0 1` also zeros the
>   upper-right block.
> - **Proved.** The two algebraic block-matrix identities, including the signs
>   and multiplication order used in Aoyagi Lemma 2.
> - **Assumed.** The determinant-unit chart hypothesis `IsUnit A1.det`.
> - **Cited.** None.
> - **Deferred.** The rank formula for the Schur complement; invertibility of
>   the triangular multipliers as local coordinate changes; all RLCT, germ,
>   ideal, and product-reduction consequences.
> - **Status.** sorry-free, axiom-clean scanner clean, targeted and full
>   `DLNFibre` builds pass; xhigh statement/fidelity review by `Euclid`.
