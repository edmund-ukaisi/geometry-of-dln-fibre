# Statement card - A2 continuous-edge signed-box continuous-density finite-integral bridge

> **Claim.** A globally continuous reversed-edge family supplies the
> source-stratum measurability and fixed-basis edge-matrix measurability
> hypotheses for the signed-box continuous-density p.13 finite-integral bridge.
>
> - **Lean target:**
>   `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_continuousEdge_continuousAt_pos_density`.
> - **Gloss.** Global `Continuous Cedge` gives source-rank-stratum
>   measurability by the existing determinantal rank-locus theorem and gives
>   fixed-basis endpoint edge-matrix measurability by composing with
>   `continuous_linearMap_toMatrix`.
> - **Proved.** A direct finite-integral handoff producing `R`, `C`, and `U`
>   with `0 < R`, `R ≤ Rmax`, `0 ≤ C`, `IsOpen U`, and `x0 ∈ U`.
> - **Assumed.** Fixed-base source data, global `Continuous Cedge`, `0 < t`,
>   signed-box chart a.e.-measurability, source-density
>   a.e.-measurability/nonnegativity/upper bound, weighted source pushforward,
>   signed-box residual monomial lower bound, `ContinuousAt density (x0,0)`,
>   `0 < density (x0,0)`, and the local regular-fiber loss lower bound.
> - **Cited.** None.
> - **Deferred.** Source-rank openness, chart construction, source-measure
>   pushforward proof, Jacobian/prior-density transport, original-loss
>   comparison, normal crossings, pole order, and RLCT extraction.
> - **Kill conditions.** This theorem is not available from only
>   `ContinuousAt Cedge x0`, does not assert raw `Measurable Cedge`, and is not
>   an analytic chart or density-transport theorem.
