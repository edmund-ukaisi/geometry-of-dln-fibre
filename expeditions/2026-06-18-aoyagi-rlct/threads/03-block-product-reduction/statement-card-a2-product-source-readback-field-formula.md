> **Claim.** For a raw multi-edge p.13 product-coordinate edge family, source
> readback has passive fields `A1passive = 1` and `A3passive = 0`, first
> regular right field `F2`, zero later right fields, residual factors `C`, and
> endpoint fields `Ctop` and `F3`.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback_productCoordinate_fields_succSucc`
>   (`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean` @ `deb9150d`)
> - **Supporting Lean:**
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.transformedEdge_productCoordinateRightEndpoint_succSucc`,
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.transformedEdge_productCoordinateLeftEndpoint_succSucc`,
>   and
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.transformedEdge_productCoordinateMiddle_succSucc`
>   (`lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean` @ `deb9150d`)
> - **Gloss.** Under the raw p.13 left/middle/right block-pattern hypotheses
>   and `IsUnit Ctop.det`, the deterministic retained-passive `sourceReadback`
>   returns exactly the displayed product-coordinate fields.
> - **Proved.** Finite block algebra for arbitrary finite endpoint types and
>   any chain with at least two product-coordinate edges.  The readback keeps
>   the supplied `Ctop`, first `F2`, `F3`, and residual factors `C`, and it
>   replaces the retained passive fields by canonical `1` and `0` values.
> - **Assumed.** The raw edge family satisfies the stated p.13 product-coordinate
>   block patterns, and `Ctop.det` is a unit.
> - **Cited.** none.
> - **Landed downstream.** The endpoint fixed-base Euclidean
>   `productSourceChart` instantiation now exists generically as
>   `paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_sourceReadback_fields`
>   and concretely in Case 2 as
>   `case2PassiveThetaEndpointProductSourceChart_sourceReadback_fields`.
> - **Deferred.** All source-prior/Haar/normal-crossing/RLCT transport.
> - **Structure & ideas observed.** The suffix recursion processes the right
>   endpoint first, converting the transformed lower-left block `-F3` into the
>   accumulated lower-unitriangular suffix field `+F3`.  Middle edges preserve
>   `B = 0`, `Ctop = 1`, and that `F3` suffix field.  The left endpoint then
>   creates `B = -F2` and `Ctop = Ctop`; source-readback negates `B` to recover
>   the first `F2`.
> - **Route.** Expose the transformed-edge shapes already implicit in the
>   residual-product proof, then combine them with the source-readback
>   definitions and the suffix-state `F2full = -B` lemma.
> - **Status.** sorry-free + controller checked.  Verification: focused
>   `ProductReduction`, focused `RetainedPassiveCoordinates`, focused
>   `RetainedPassiveCase2PassiveThetaSourceImage`, focused source-image module
>   build, full `lake build DLNFibre`, `scripts/sorries`, `git diff --check`,
>   and axiom probe passed.  Axiom footprint:
>   `[propext, Classical.choice, Quot.sound]`.
