# Statement card - A2 signed-box residual source finite-integral bridge

> **Claim.** Weighted signed-box residual source data can supply the residual
> positivity and residual negative-power integrability hypotheses required by
> the p.13 local finite-integral bridge.
>
> - **Lean target:**
>   `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix`,
>   composing
>   `residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_edgeMatrix`
>   with
>   `exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top`.
> - **Gloss.** The signed-box theorem gives the source-stratum residual
>   positivity/integrability pair; the p.13 theorem consumes that pair together
>   with source-stratum measurability and local regular-fiber loss/density
>   bounds.
> - **Proved.** A direct finite-integral handoff from signed-box residual
>   source hypotheses to the local p.13 finite-integral conclusion.
> - **Assumed.** Fixed-base source data, source-stratum measurability,
>   fixed-basis edge-matrix measurability, `0 < t`, signed-box chart
>   a.e.-measurability, source-density a.e.-measurability, weighted source
>   pushforward, signed-box residual monomial lower bound, signed-box density
>   a.e. nonnegativity, signed-box density monomial upper bound, and the local
>   regular-fiber loss/density bounds.
> - **Cited.** None.
> - **Deferred.** Chart construction, source-measure pushforward proof,
>   Jacobian/prior-density transport, original-loss comparison, normal
>   crossings, pole order, and RLCT extraction.
> - **Kill conditions.** This is not an analytic chart theorem and not a proof
>   of the regular-fiber loss lower bound.
