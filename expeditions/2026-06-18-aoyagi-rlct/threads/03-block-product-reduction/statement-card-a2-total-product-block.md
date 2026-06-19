# Statement card - A2 total-product endpoint block

> **Claim.** If the source complement is the kernel of the total chain map,
> then the total product has endpoint matrix block form `[I 0; 0 0]` in
> transported direct-sum bases.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.toMatrix_chainMap_zero_last_ker_basisOfIsCompl_eq_fromBlocks_one_zero_zero`
>   and
>   `DLNFibre.DLN.Aoyagi.toMatrix_chainMap_zero_last_ker_finiteDimensional_eq_fromBlocks_one_zero_zero`
>   and the paper-order wrapper
>   `DLNFibre.DLN.Aoyagi.toMatrix_paperChainMap_ker_finiteDimensional_eq_fromBlocks_one_zero_zero`
>   (`lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`).
> - **Gloss.** Let `P = chainMap V A 0 (Fin.last N) ...`. Choose
>   `U₀` complementary to `ker P`, choose any complement `Wlast` to
>   `throughSubspace V A U₀ (Fin.last N)`, and use `basisOfIsCompl` with a
>   basis of `U₀`, a basis of `ker P`, and a basis of `Wlast`. Transport the
>   `U₀` basis to the target through-subspace using
>   `linearEquivMapOfDisjointKer P U₀ hU₀.disjoint`. In these endpoint bases,
>   the matrix of `P` is `fromBlocks 1 0 0 0`. The finite-dimensional wrapper
>   uses the chosen target complement `throughSubspaceComplement` and
>   `Module.finBasis` for all three basis choices.
> - **Proved.** The generic zero-column direct-sum lemma
>   `toMatrix_basisOfIsCompl_eq_fromBlocks_one_zero_zero_of_map_complement_eq_zero`
>   and its chain-map specialization. The zero complement columns come from the
>   source complement being `ker P`.
> - **Assumed.** Generic theorem: explicit complement
>   `hU₀ : IsCompl U₀ (ker P)`, explicit target complement `hWlast`, and
>   explicit bases of `U₀`, `ker P`, and `Wlast`, with finite/decidable source
>   indices for `LinearMap.toMatrix`. Finite-dimensional wrapper:
>   `[∀ j, FiniteDimensional K (V j)]` and `hU₀`; the remaining complement and
>   basis choices are chosen noncomputably.
> - **Cited.** None.
> - **Deferred.** Connecting the per-edge and endpoint block forms to the
>   chart-local product-reduction identity; full Aoyagi Theorem 3; and every
>   analytic/RLCT consequence.
> - **Kill conditions.** The theorem is not a fixed-coordinate statement and
>   does not say arbitrary endpoint bases give `[I 0; 0 0]`. The source
>   complement must be the total kernel, and the target through-basis must be
>   transported from the source through-basis.
