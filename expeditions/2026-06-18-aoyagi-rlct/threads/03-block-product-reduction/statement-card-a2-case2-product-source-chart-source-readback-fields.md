> **Claim.** For the concrete Case 2 endpoint fixed-base p.13 product source
> chart, `sourceReadback` returns canonical retained passive fields, the
> regular fields decoded from `u`, and the residual factors extracted from the
> passive-theta base source family.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.case2PassiveThetaEndpointProductSourceChart_sourceReadback_fields`
>   (`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean`)
> - **Supporting Lean:**
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback_productCoordinate_fields_succSucc`
>   (`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`) and
>   `paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean`
>   (`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`).
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
> - **Structure & ideas observed.** The proof defines the fixed-base base
>   matrices `Ebase`, the product matrices `Eprod`, and the prescribed product
>   matrix family `G`.  The realisation theorem identifies `Eprod = G`; the
>   endpoint cases unfold to the raw p.13 shapes, and the middle case is
>   vacuous because the Case 2 chain has only two edges.
> - **Route.** Instantiate
>   `sourceReadback_productCoordinate_fields_succSucc` with `N = 0`, residual
>   factors `residualBlock Ebase`, and the regular fields decoded from `u`.
> - **Status.** sorry-free + controller checked + xhigh review PASS.  The
>   reviewer noted only Lean/API fragility from endpoint proofs using
>   definitional unfolding plus `simp ...; rfl`, not mathematical overreach.
>   Verification: focused direct check, focused module build, full local
>   `lake build DLNFibre`, `scripts/sorries`, `git diff --check`, and direct
>   axiom probe passed.  Axiom footprint:
>   `[propext, Classical.choice, Quot.sound]`.
