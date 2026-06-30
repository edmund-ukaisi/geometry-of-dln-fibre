> **Claim.** For the generic endpoint fixed-base source-dependent p.13 product
> coordinate edge family, source-readback returns canonical retained passive
> fields, the regular fields decoded from `u`, and the residual blocks
> extracted from the base fixed-base edge family.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_sourceReadback_fields`
>   (`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSourceReadback.lean`)
> - **Supporting Lean:**
>   `paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean`
>   and `paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean`
>   (`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`), plus
>   `ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback_productCoordinate_fields_succSucc`
>   (`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`).
> - **Gloss.** For any base family `CedgeBase x`, fixed-base product edge
>   matrices realised by the p.13 constructor have the raw left/middle/right
>   product-coordinate shapes.  Therefore the raw retained-passive
>   source-readback theorem applies.
> - **Proved.** Pointwise field formula for arbitrary finite chain length:
>   `A1passive = 1`, `F2 = first decoded F2 then zeros`,
>   `A3passive = 0`, `C = residualBlock(fixedBase(CedgeBase x))`,
>   `Ctop = decoded Ctop`, and `F3 = decoded F3`, assuming
>   `IsUnit (ctopMatrix u).det`.
> - **Assumed.** The fixed-base chart hypotheses and determinant-unit
>   condition on decoded `Ctop`.
> - **Cited.** none.
> - **Deferred.** Full parameter recovery, original/source-prior transport,
>   Haar/Jacobian density identities, source-image coverage/equality, normal
>   crossings, pole order, and RLCT.
> - **Structure & ideas observed.** The proof centralizes the previous
>   endpoint-shape unfolding: identify `Eprod` with the prescribed matrix
>   family `G`, discharge the left/middle/right raw p.13 shape hypotheses, and
>   call the raw `sourceReadback_productCoordinate_fields_succSucc` theorem.
> - **Route.** New bridge module imports both `RegularSuspensionCoordinates`
>   and `RetainedPassiveCoordinates`; the concrete Case 2 source-image theorem
>   now delegates to this generic theorem with `M = 0`.
> - **Status.** sorry-free + controller checked + xhigh review PASS.  The
>   reviewer noted only Lean/API fragility from definitional unfolding of the
>   product-coordinate matrix constructor, not mathematical overreach.
>   Verification: focused direct checks, focused module builds, aggregator
>   direct check, full local `lake build DLNFibre`, `scripts/sorries`,
>   `git diff --check`, and direct axiom probe passed.  Axiom footprint:
>   `[propext, Classical.choice, Quot.sound]`.
