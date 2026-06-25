# Statement card - A2 signed-box residual continuous-density finite-integral bridge

> **Claim.** Weighted signed-box residual source data and a positive continuous
> transported density factor supply the residual and local-density hypotheses
> required by the p.13 radius-shrinking local finite-integral bridge.
>
> - **Lean target:**
>   `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_continuousAt_pos_density`,
>   composing
>   `residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_edgeMatrix`
>   with
>   `exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_continuousAt_pos_density`.
> - **Gloss.** The signed-box theorem gives source residual
>   positivity/integrability.  The continuous-density theorem shrinks the
>   regular-coordinate radius to obtain density nonnegativity and boundedness.
> - **Proved.** A direct finite-integral handoff from signed-box residual
>   source hypotheses and continuous positive product density to the local p.13
>   radius-shrinking finite-integral conclusion, producing a radius `R` with
>   `0 < R` and `R ≤ Rmax`.
> - **Assumed.** Fixed-base source data, source-stratum measurability,
>   fixed-basis edge-matrix measurability, `0 < t`, signed-box chart
>   a.e.-measurability, source-density a.e.-measurability, weighted source
>   pushforward, signed-box residual monomial lower bound, source-density
>   a.e. nonnegativity, source-density monomial upper bound,
>   `ContinuousAt density (x0,0)`, `0 < density (x0,0)`, and the local
>   regular-fiber loss lower bound.
> - **Cited.** None.
> - **Deferred.** Chart construction, source-measure pushforward proof,
>   Jacobian/prior-density transport, original-loss comparison, normal
>   crossings, pole order, and RLCT extraction.
> - **Kill conditions.** This is not an analytic chart theorem, not a density
>   transport theorem, and not a proof of the regular-fiber loss lower bound.
