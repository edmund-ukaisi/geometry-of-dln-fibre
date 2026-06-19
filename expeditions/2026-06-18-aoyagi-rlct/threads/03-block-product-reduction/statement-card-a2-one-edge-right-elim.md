# Statement card - A2 one-edge right elimination

> **Claim.** If a current prefix has block-diagonal form and the next adapted
> edge has identity-corner form `[I B; 0 D]`, then multiplying on the right by
> the corresponding upper-unitriangular source-side block eliminates the
> top-right block and extends the residual prefix from `Dprev` to
> `Dprev * D`.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.upperRightBlock`,
>   `DLNFibre.DLN.Aoyagi.lowerRightBlock`,
>   `DLNFibre.DLN.Aoyagi.productReduction_blockDiagonal_mul_fromBlocks_one_zero_rightElim_indexed`,
>   `DLNFibre.DLN.Aoyagi.productReduction_blockDiagonal_mul_eq_fromBlocks_one_zero_rightElim_indexed`,
>   convenience wrapper
>   `DLNFibre.DLN.Aoyagi.productReduction_blockDiagonal_mul_identityCornerForm_rightElim`,
>   deterministic wrappers
>   `DLNFibre.DLN.Aoyagi.productReduction_blockDiagonal_mul_identityCornerForm_rightElim_submatrix`
>   and
>   `DLNFibre.DLN.Aoyagi.productReduction_blockDiagonal_mul_unitriangular_identityCornerForm_rightElim`
>   (`lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`) and paper-order
>   corollary
>   `DLNFibre.DLN.Aoyagi.productReduction_paperAdaptedReverseEdgeMatrix_rightElim`
>   (`lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`).
> - **Gloss.** The bedrock theorem proves the explicit witnessed identity
>   `fromBlocks C1 0 0 Dprev * fromBlocks 1 B 0 Dnext *
>   fromBlocks 1 (-B) 0 1 = fromBlocks C1 0 0 (Dprev * Dnext)`.
>   The equality corollary allows an explicit hypothesis
>   `M = fromBlocks 1 B 0 Dnext`. The convenience theorem packages the same
>   identity through `identityCornerForm`, returning the required witness `B`
>   existentially:
>   `fromBlocks C1 0 0 Dprev * M * fromBlocks 1 (-B) 0 1 =
>   fromBlocks C1 0 0 (Dprev * Dnext)` from the witness
>   `M = fromBlocks 1 B 0 Dnext`. The paper corollary applies this to
>   `paperAdaptedReverseEdgeMatrix`. For that corollary the residual columns of
>   `Dprev` are indexed by the edge target complement at `p.succ`, while the
>   right multiplier acts on the edge source complement at `p.castSucc`.
>   The deterministic submatrix theorem chooses `B = upperRightBlock M` and
>   `Dnext = lowerRightBlock M`, avoiding an existential witness in the next
>   induction step. The unitriangular theorem packages the accumulated
>   upper-left chart transform before applying the same deterministic
>   elimination.
> - **Proved.** Pure block-matrix multiplication over a commutative ring, with
>   the explicit indexed identity stated over a `NonAssocRing`; no
>   determinant-unit hypothesis. The paper-order version is an instantiation
>   using the already proved adapted edge identity-corner form.
> - **Assumed.** Matrix dimensions encoded by types; field and
>   finite-dimensional layer hypotheses only for the paper-order wrapper.
> - **Cited.** None.
> - **Deferred.** Iterating this step through all paper layers; suffix-oriented
>   chain-reduction induction; rank-stratum statements; topological
>   open-neighborhood statements; target normalization; and every analytic/RLCT
>   consequence.
> - **Kill conditions.** This is not Aoyagi Theorem 3. It does not say that
>   fixed-coordinate layer blocks are invertible, that a local chart is open, or
>   that the reduced residual product has the correct RLCT.
