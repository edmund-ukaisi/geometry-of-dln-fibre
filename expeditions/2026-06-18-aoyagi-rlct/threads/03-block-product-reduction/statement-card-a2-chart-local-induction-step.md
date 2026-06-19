# Statement card - A2 chart-local induction step

> **Claim.** On a chart where the already-isolated prefix corner `C1` and the
> next-layer corner `A1` have unit determinant, the next Aoyagi product-reduction
> induction step is the displayed two-sided block multiplication identity.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.productReduction_chartLocalInductionStep_fromBlocks`
>   (`lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean` @ `7a30e80`)
> - **Gloss.** For matrices over a commutative ring, assume
>   `hC1 : IsUnit C1.det` and `hA1 : IsUnit A1.det`. Then multiplying
>   `(fromBlocks C1 0 0 D * fromBlocks A1 A2 A3 A4)` on the left by
>   `fromBlocks 1 0 (-(D * A3 * (C1 * A1)⁻¹)) 1` and on the right by
>   `fromBlocks 1 (-(A1⁻¹ * A2)) 0 1` gives
>   `fromBlocks (C1 * A1) 0 0 (D * (A4 - A3 * A1⁻¹ * A2))`.
> - **Proved.** The chart-local algebraic block identity used for one
>   induction step in Aoyagi's product reduction, including the signs,
>   multiplication order, and the residual Schur-complement factor.
> - **Assumed.** Matrix dimensions encoded by the `Fin` indices, and the
>   determinant-unit chart hypotheses `IsUnit C1.det` and `IsUnit A1.det`.
>   The file includes an identity-corner example witnessing that these chart
>   hypotheses are inhabited, including the zero-size case.
> - **Cited.** None.
> - **Deferred.** The full Aoyagi Theorem 3 reduction from rank/neighborhood
>   hypotheses; the through-layer basis/open-chart existence lemma; target
>   product normalization via Aoyagi Lemma 1; local analytic/ideal-germ
>   invariance; regular-coordinate RLCT additivity; and every final RLCT
>   consequence.
> - **Status.** sorry-free, axiom-clean scanner clean, targeted and full
>   `DLNFibre` builds pass; xhigh hardener `Jason` and xhigh fidelity reviewer
>   `Huygens` pass at this narrow chart-local scope.
