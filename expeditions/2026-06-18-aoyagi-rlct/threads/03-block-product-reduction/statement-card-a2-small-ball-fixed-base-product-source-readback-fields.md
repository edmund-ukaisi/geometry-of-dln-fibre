> **Claim.** After shrinking the p.13 regular Euclidean variables around
> `0`, the fixed-base product-coordinate source-readback field formula holds
> uniformly in the base edge-family point.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.exists_pos_radius_le_forall_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_sourceReadback_fields`
>   (`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSourceReadback.lean`)
> - **Concrete Lean wrapper:**
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_sourceReadback_fields`
>   (`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean`)
> - **Supporting Lean:**
>   `AoyagiRegularBlockCoordinateIndex.exists_pos_radius_le_forall_isUnit_det_ctopMatrix_euclidean`
>   and
>   `paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_sourceReadback_fields`.
> - **Gloss.** Since `Ctop(0) = I` and determinant is continuous, there is a
>   radius `R > 0`, with `R ≤ Rmax`, such that every `u` in `ball(0,R)` has
>   `IsUnit (det Ctop(u))`.  The pointwise fixed-base source-readback theorem
>   then applies for every base point `x`.
> - **Proved.** A uniform small-ball field package:
>   `A1passive = 1`, `F2 = first decoded F2 then zeros`,
>   `A3passive = 0`, `C = residualBlock(fixedBase(CedgeBase x))`,
>   `Ctop = decoded Ctop`, and `F3 = decoded F3`.  The concrete Case 2 wrapper
>   gives the same package for every passive-theta base point.
> - **Assumed.** Only the fixed-base chart hypotheses and `0 < Rmax`; the
>   determinant-unit condition is discharged by shrinking the regular ball.
> - **Cited.** none.
> - **Deferred.** Full parameter recovery, source-prior transport,
>   Haar/Jacobian density identities, source-image coverage/equality, normal
>   crossings, pole order, and RLCT.
> - **Structure & ideas observed.** The proof is a wrapper around the
>   determinant-unit radius lemma and the pointwise fixed-base readback fields.
>   The radius is independent of the base point.
> - **Route.** Choose the radius from the `ctopMatrix` unit lemma, then call
>   the pointwise fixed-base product source-readback theorem with the supplied
>   `hunit u hu`.
> - **Status.** sorry-free + controller checked + xhigh review PASS.  The
>   reviewer noted only non-blocking Lean/API fragility from large `simpa`
>   calls over local `let`s in these thin wrapper theorems.  Verification:
>   focused direct checks, focused module builds, full local
>   `lake build DLNFibre`, `scripts/sorries`, `git diff --check`, and direct
>   axiom probe passed.  Axiom footprint:
>   `[propext, Classical.choice, Quot.sound]`.
