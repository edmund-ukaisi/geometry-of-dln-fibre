# Statement card - A2 residual zero-locus handoff

> **Claim.** If the residual coordinate square-sum has null zero locus on a
> source set, then it is positive almost everywhere on that source set; combined
> with finite residual negative-power integral, this gives the residual
> hypotheses on any smaller source set.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.ae_pos_of_forall_nonneg_of_measure_zero_eq_zero`
>   (`lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean`),
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.residualSquareSum_pos_ae_of_zero_set_null`,
>   and
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_mono_of_zero_set_null`
>   (`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean`).
> - **Gloss.** For a nonnegative real function, the failure of strict positivity
>   is contained in the zero locus.  The residual square-sum is nonnegative
>   because it is a finite sum of squares.
> - **Pen-and-paper check.** `{x | not 0 < f x} subset {x | f x = 0}` follows
>   from `0 <= f x`; nullity transfers by monotonicity of measure.
> - **Proved.** Residual a.e. positivity from residual zero-locus nullity; the
>   positivity/integrability pair transfers to smaller source sets.
> - **Assumed.** The residual zero locus is null, and the residual negative-power
>   integral is finite on the larger source set.
> - **Cited.** None.
> - **Deferred.** Nullity of the residual zero locus, residual negative-power
>   integrability, source/chart measure transport, original-loss comparison,
>   normal crossings, pole order, and RLCT extraction.
> - **Kill conditions.** Do not read this as a generic proof that Aoyagi's
>   residual zero locus is negligible.  That remains a chart/source-measure
>   theorem.
