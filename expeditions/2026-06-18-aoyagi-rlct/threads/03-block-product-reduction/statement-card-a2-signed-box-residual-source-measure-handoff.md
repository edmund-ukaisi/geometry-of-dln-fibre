# Statement card - A2 signed-box residual source-measure handoff

> **Claim.** If the restricted source measure is supplied as the pushforward
> of an unweighted signed-box product measure, and the chart-side residual
> square is bounded below a.e. by a positive constant times
> `product_i |y_i|^(2*k_i)`, then the residual positivity and residual
> negative-power integrability hypotheses hold on the source under
> `t >= 0` and `2*t*k_i < 1` for every coordinate.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.lintegral_ofReal_loss_rpow_neg_signedBox_lt_top`
>   (`lean/DLNFibre/DLN/Aoyagi/MonomialChartIntegrability.lean`) and
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_of_measure_map_signedBox_monomialLower`
>   (`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean`).
> - **Gloss.** Signed boxes avoid every coordinate hyperplane a.e.; the lower
>   bound makes the residual square positive a.e.  The same lower bound
>   compares `residualSq^(-t)` to an integrable product of
>   `|y_i|^(-2*t*k_i)`, and the supplied source pushforward transports the
>   chart-side facts to the source.
> - **Pen-and-paper check.** On the full-measure set where all coordinates are
>   nonzero and the lower bound holds,
>   `0 < c*product_i |y_i|^(2*k_i) <= residualSq(chart y)`.  Since `t >= 0`,
>   `residualSq(chart y)^(-t) <= c^(-t)*product_i |y_i|^(-2*t*k_i)`; each
>   one-dimensional signed finite-side integral is finite when
>   `2*t*k_i < 1`.
> - **Proved.** The density-free signed-box finite-integral comparison, and
>   the exact residual positivity/integrability pair on the source from a
>   supplied signed-box pushforward and supplied residual monomial lower bound.
> - **Assumed.** A.e.-measurability of the chart map, measurability of the
>   positive residual set, the source-measure pushforward identity, positive
>   side lengths `R_i`, `c > 0`, `t >= 0`, the strict coordinate inequalities
>   `2*t*k_i < 1`, and the a.e. residual monomial lower bound.
> - **Cited.** None.
> - **Deferred.** Construction of Aoyagi's chart, proof of the pushforward
>   identity, Jacobian/density transport, density-weighted exponent bounds,
>   original-loss comparison, normal crossings, pole order, and RLCT
>   extraction.
> - **Kill conditions.** Do not read this as a Jacobian theorem, a
>   chart-construction theorem, or the full Aoyagi `h_i`-weighted finite-side
>   calculation.  It is only the unweighted signed-box source-measure
>   constructor.
