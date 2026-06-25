# Statement card - A2 residual positive-set measurability handoff

> **Claim.** If the p.13 residual coordinate map is measurable, then the
> residual square-sum positive set is measurable.  Consequently, the weighted
> signed-box residual source-measure constructor can derive its positive-set
> measurability premise instead of requiring it as a separate hypothesis.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.measurable_aoyagiCoordinateSquareSum`,
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.measurableSet_residualSquareSum_pos_of_measurable`,
>   and
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_residual`.
> - **Gloss.** A finite square-sum is a finite sum of products of measurable
>   scalar coordinates, hence measurable.  The positive set is the preimage of
>   `Set.Ioi 0`.  The weighted signed-box corollary feeds this measurable set
>   into the existing residual source-measure handoff.
> - **Proved.** Positive-set measurability from measurable residual coordinates,
>   and a weighted signed-box residual handoff without an explicit `hpos_meas`
>   argument.
> - **Assumed.** Global measurability of the residual coordinate map,
>   a.e.-measurability of `ofReal density`, a.e.-measurability of the chart on
>   the signed box, the weighted pushforward identity, positive side lengths,
>   `c > 0`, `C >= 0`, `t >= 0`, strict coordinate inequalities
>   `2*t*k_i < h_i+1`, and the signed-box a.e. residual and density bounds.
> - **Cited.** None.
> - **Deferred.** Deriving residual-coordinate measurability from the full
>   deterministic p.13 suffix-state recursion, chart construction, pushforward
>   identity, Jacobian/density construction, original-loss comparison, normal
>   crossings, pole order, and RLCT extraction.
> - **Kill conditions.** This is not residual positivity or integrability by
>   itself, and not a global measurability theorem for the residual chart.
