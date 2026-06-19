# Statement card - A2 suffix-chain right elimination

> **Claim.** A chain of identity-corner edge matrices can be right-eliminated,
> suffix-first, to block-diagonal form by one upper-unitriangular multiplier on
> the source side.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.productReduction_identityCorner_suffixChain_rightElim`
>   (`lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`), plus supplied adapted
>   matrix wrapper
>   `DLNFibre.DLN.Aoyagi.productReduction_throughSubspaceAdaptedChainMapMatrix_suffixChain_rightElim`
>   and helper theorems
>   `DLNFibre.DLN.Aoyagi.throughSubspaceAdaptedChainMapMatrix_proof_irrel`,
>   `DLNFibre.DLN.Aoyagi.throughSubspaceAdaptedChainMapMatrix_self`, and
>   `DLNFibre.DLN.Aoyagi.identityCornerForm_throughSubspaceAdaptedEdgeMatrix`
>   (`lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`).
> - **Gloss.** The abstract theorem assumes edge matrices `E p` have
>   `identityCornerForm`, a segment matrix family `P i j` has identity empty
>   segments, and suffix composition satisfies `P p.castSucc j = P p.succ j *
>   E p`. It then proves existence of `B` and `D` with
>   `P i j * [I -B; 0 I] = [I 0; 0 D]`.
> - **Proved.** Pure matrix algebra over a commutative ring, plus the supplied
>   through-subspace adapted-basis instantiation.
> - **Assumed.** Finite/decidable matrix index families. The abstract theorem
>   also assumes proof-irrelevance of `P i j h` in the order proof `h`; the
>   supplied adapted matrix wrapper discharges this by
>   `throughSubspaceAdaptedChainMapMatrix_proof_irrel`.
> - **Cited.** None.
> - **Deferred.** Rank/open-neighborhood bridge, target normalization,
>   identification with Aoyagi's named residual factors, and every
>   analytic/RLCT consequence. The paper-order endpoint packaging is now a
>   separate proved wrapper, not part of this abstract card.
> - **Review.** Xhigh review found no orientation blocker and confirmed that
>   `hPproof` is Lean proof bookkeeping, not a mathematical assumption. It
>   flagged the source-fidelity boundary that the supplied wrapper is pointwise
>   and basis-dependent.
> - **Kill conditions.** This is not full Aoyagi Theorem 3. It does not assert
>   a local chart is open, that fixed coordinate pivots exist near a base point,
>   or that the residual block has the source paper's rank/RLCT interpretation.
