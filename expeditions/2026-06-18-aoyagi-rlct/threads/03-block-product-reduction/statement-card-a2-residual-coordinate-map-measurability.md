# Statement card - A2 residual-coordinate map measurability

> **Claim.** If the reversed edge family is measurably given as fixed-basis
> endpoint edge matrices, then the p.13 fixed-base residual `D`-block coordinate
> map is measurable.  Consequently, the weighted signed-box residual
> source-measure constructor can derive the residual positive-set
> measurability premise from that fixed-basis edge-matrix measurability.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.measurable_matrix_inv_real`,
>   `DLNFibre.DLN.Aoyagi.measurable_chartLocalSuffixState_suffixState_fields_real`,
>   `DLNFibre.DLN.Aoyagi.measurable_paperEndpointFixedBaseResidualBlockCoordinateMap_of_measurable_edgeMatrix`,
>   and
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_edgeMatrix`.
> - **Gloss.** The suffix-state update is a finite composition of measurable
>   real matrix operations.  Matrix inverse is totalized and Borel measurable,
>   so the residual `D` block remains measurable through the recursion.
> - **Proved.** Measurability of the deterministic suffix-state fields from a
>   measurable real edge-matrix family; measurability of the fixed-base residual
>   coordinate map from measurable fixed-basis edge matrices; a weighted
>   signed-box residual handoff without a separate `hres_meas` argument under
>   that hypothesis.
> - **Assumed.** Finite-dimensional real endpoint data, a fixed complement
>   `U0`, fixed-basis edge-matrix measurability, and all existing signed-box
>   chart, pushforward, monomial residual lower-bound, and density hypotheses
>   in the local-measure consumer.
> - **Cited.** None.
> - **Deferred.** Raw `Measurable Cedge` for arbitrary non-normed
>   continuous-linear-map spaces, p.13 chart construction, source-measure
>   pushforward, Jacobian/density construction, original-loss comparison,
>   residual positivity/integrability without signed-box hypotheses, normal
>   crossings, pole order, and RLCT extraction.
> - **Kill conditions.** This is not a determinant-chart theorem, not a
>   source-rank openness theorem, and not a chart or RLCT theorem.  Do not use it
>   from only local continuity at the base point.
