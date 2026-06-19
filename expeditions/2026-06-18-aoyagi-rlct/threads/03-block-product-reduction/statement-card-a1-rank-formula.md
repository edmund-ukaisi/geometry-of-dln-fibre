# Statement card - A1 rank formula

> **Claim.** On the chart where the top-left block `A1` has unit determinant,
> the rank of `fromBlocks A1 A2 A3 A4` is the corner size plus the rank of the
> Schur complement `A4 - A3 * A1⁻¹ * A2`.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.rank_fromBlocks_zero_zero` and
>   `DLNFibre.DLN.Aoyagi.rank_fromBlocks_eq_card_add_rank_schurComplement_of_isUnit_det`
>   (`lean/DLNFibre/DLN/Aoyagi/BlockElimination.lean` @ `74e4972`)
> - **Gloss.** Over a field, block-diagonal matrix rank is additive. Combining
>   that with the algebraic block-elimination identities and rank invariance
>   under determinant-unit left/right multiplication gives
>   `rank [A1 A2; A3 A4] = r + rank(A4 - A3 * A1⁻¹ * A2)`.
> - **Proved.** The reusable block-diagonal rank theorem and Aoyagi Lemma 2's
>   Schur-complement rank formula in additive form.
> - **Assumed.** Field scalars for rank additivity and the determinant-unit
>   chart hypothesis `IsUnit A1.det`.
> - **Cited.** None.
> - **Deferred.** Local analytic coordinate-change consequences; RLCT, germ,
>   ideal, and product-reduction consequences.
> - **Status.** sorry-free, axiom-clean scanner clean, targeted and full
>   `DLNFibre` builds pass; xhigh fidelity review by `Euclid`.
