# Statement card - A2 continuous density local bounds

> **Claim.** If the supplied p.13 density factor is positive and continuous at
> the chart center, then after shrinking the regular-coordinate radius it
> satisfies the local nonnegativity and upper-bound hypotheses needed by the
> local finite-integral bridge.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.exists_pos_radius_le_eventually_density_bounds_of_continuousAt_pos`,
>   `DLNFibre.DLN.Aoyagi.exists_pos_radius_le_eventually_nhdsWithin_density_bounds_of_continuousAt_pos`
>   (`lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean`),
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_mono`,
>   and
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_continuousAt_pos_density`
>   (`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean`).
> - **Gloss.** Continuity at `(x0,0)` pulls back the interval
>   `(0, density(x0,0)+1)` to a product neighborhood.  A small regular-coordinate
>   ball inside the fiber neighborhood gives `0 <= density <= C`; the
>   source-relative version weakens the base filter to `nhdsWithin`.
> - **Pen-and-paper check.** Pick `C=density(x0,0)+1`, then choose `U,V` with
>   `U x V` mapping into `(0,C)`.  Pick `R <= Rmax` with `ball(0,R) ⊆ V`.
> - **Proved.** Local density nonnegativity and boundedness from positive
>   continuity; residual positivity/integrability restriction to smaller source
>   sets; a p.13 finite-integral wrapper consuming the continuous-density input.
> - **Assumed.** The density function itself, its continuity and positivity at
>   the center, source-stratum measurability, residual positivity and
>   integrability, and the loss lower bound on the larger radius cap.
> - **Cited.** None.
> - **Deferred.** Construction of the density/Jacobian factor, actual
>   Jacobian/prior transport, original-loss comparison, residual
>   positivity/integrability proof, normal-crossing production, pole order, and
>   RLCT extraction.
> - **Kill conditions.** Do not read this as a chart-Jacobian theorem.  It only
>   bounds a density factor after that factor has been supplied.
