# Statement card - A2 residual source-measure map handoff

> **Claim.** If the restricted source measure is supplied as the pushforward of
> a chart-side measure, and residual positivity plus residual negative-power
> integrability hold after pulling back to the chart side, then the residual
> source hypotheses required by the p.13 finite-integral bridge hold on the
> source.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_of_measure_map`
>   (`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean`).
> - **Gloss.** A.e. positivity transports by `ae_map_iff`; the finite lower
>   integral transports by the inequality `lintegral_map_le`.
> - **Pen-and-paper check.** Substitute
>   `mu.restrict source = Measure.map chart nu`.  A.e. statements pull back
>   along the map, and the lower integral on the pushforward is bounded by the
>   chart-side lower integral of the pullback.
> - **Proved.** The exact residual positivity/integrability pair on the source
>   from supplied chart-side positivity/integrability and supplied pushforward
>   measure identity.
> - **Assumed.** A.e.-measurability of the chart map, measurability of the
>   positive residual set, the source-measure pushforward identity, chart-side
>   residual positivity, and chart-side finite residual negative-power integral.
> - **Cited.** None.
> - **Deferred.** Construction of Aoyagi's chart, proof of the pushforward
>   identity, Jacobian/density transport, monomial residual bounds,
>   original-loss comparison, normal crossings, pole order, and RLCT extraction.
> - **Kill conditions.** Do not read this as a Jacobian theorem or as a proof
>   that Aoyagi's residual hypotheses hold.  It only transports already-supplied
>   chart-side hypotheses across an already-supplied measure map.
