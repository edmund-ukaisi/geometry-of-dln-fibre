# Statement card - A2 weighted signed-box residual source-measure handoff

> **Claim.** If the restricted source measure is supplied as the pushforward
> of a signed-box product measure with supplied density
> `ofReal(density)`, and the chart-side residual and density satisfy
> absolute-monomial lower/upper bounds, then the residual positivity and
> residual negative-power integrability hypotheses hold on the source under
> `t >= 0` and `2*t*k_i < h_i + 1` for every coordinate.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower`
>   (`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean`).
> - **Gloss.** Signed boxes avoid coordinate hyperplanes a.e.; the residual
>   lower bound makes the pulled-back residual positive a.e.  The weighted
>   lower integral is rewritten using `withDensity`, then the existing
>   signed-box residual/density theorem gives finite chart-side integral.  The
>   supplied pushforward identity transports the chart-side facts to the
>   source.
> - **Pen-and-paper check.** Positivity transfers from `signedBox` to
>   `signedBox.withDensity (ofReal density)` by absolute continuity.  For the
>   integral,
>   `int^- ofReal(f^(-t)) d(withDensity ofReal density)` becomes
>   `int^- ofReal(f^(-t) * density) dsignedBox` on the a.e. set where
>   `density >= 0`, and the landed signed-box residual/density estimate applies.
> - **Proved.** The exact residual positivity/integrability pair on the source
>   from a supplied weighted signed-box pushforward plus supplied residual
>   monomial lower bound and density monomial upper bound.
> - **Assumed.** A.e.-measurability of `ofReal density` on the signed box,
>   a.e.-measurability of the chart on the signed box, measurability of the
>   positive residual set, the weighted source-measure pushforward identity,
>   positive side lengths, `c > 0`, `C >= 0`, `t >= 0`, the strict coordinate
>   inequalities `2*t*k_i < h_i+1`, and the three signed-box a.e. residual and
>   density bounds.
> - **Cited.** None.
> - **Deferred.** Construction of Aoyagi's chart, proof of the weighted
>   pushforward identity, Jacobian/density construction or continuity, original
>   loss comparison, normal crossings, pole order, and RLCT extraction.
> - **Kill conditions.** Do not read this as a Jacobian theorem or as proof
>   that Aoyagi's analytic chart supplies the density.  It is only the weighted
>   signed-box source-measure constructor once those data are supplied.
