> **Claim.** For the concrete Case 2 endpoint fixed-base p.13 product source
> chart, `sourceReadback` returns canonical retained passive fields, the
> regular fields decoded from `u`, and the residual factors extracted from the
> passive-theta base source family.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.case2PassiveThetaEndpointProductSourceChart_sourceReadback_fields`
>   (`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean`)
> - **Supporting Lean:**
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_sourceReadback_fields`
>   (`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSourceReadback.lean`).
> - **Gloss.** At a point `(theta,u)`, convert the product source chart to
>   fixed-base edge matrices.  These matrices are the p.13 left/right endpoint
>   product-coordinate shapes; in Case 2 there is no middle edge.  The raw
>   source-readback theorem then gives the field identities.
> - **Proved.** Pointwise field formula:
>   `A1passive = 1`, `F2 = first decoded F2 then zero`, `A3passive = 0`,
>   `C = residualBlock(fixedBase(sourceChart theta))`, `Ctop = decoded Ctop`,
>   and `F3 = decoded F3`, assuming `IsUnit (ctopMatrix u).det`.
> - **Assumed.** The usual Case 2 source-chart hypotheses and the p.13
>   determinant-unit condition on the decoded `Ctop` block.
> - **Cited.** none.
> - **Deferred.** Full recovery of passive theta from the product chart,
>   original/source-prior transport, Haar/Jacobian density identity,
>   source-image coverage/equality, normal crossings, pole order, and RLCT.
> - **Structure & ideas observed.** The proof now delegates to the generic
>   fixed-base product-source-readback theorem with `M = 0`; the endpoint
>   shape unfolding is centralized in the generic API.
> - **Route.** Instantiate
>   `paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_sourceReadback_fields`
>   with the concrete passive-theta endpoint source chart.
> - **Status.** sorry-free + controller checked + xhigh review PASS before
>   generic refactor.  The reviewer noted only Lean/API fragility from local
>   endpoint unfolding; the refactor removes that fragility from the concrete
>   theorem.  Verification before refactor: focused direct check, focused
>   module build, full local `lake build DLNFibre`, `scripts/sorries`,
>   `git diff --check`, and direct axiom probe passed.  Verification after
>   refactor is tracked on the generic fixed-base statement card.
