# Statement card - A2 through-layer subspaces

> **Claim.** For an upward finite chain of linear maps, a complement to the
> kernel of the total composite gives subspaces through every layer which are
> transported by the edge maps and have dimension equal to the rank of the
> total composite.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.exists_chain_throughSubspaces`
>   (`lean/DLNFibre/DLN/Aoyagi/ThroughLayerBasis.lean`).
> - **Gloss.** For `A i : V i.castSucc -> V i.succ`, let `P` be the composite
>   `V 0 -> V (Fin.last N)`. There are subspaces `U 0, ..., U last` with
>   `U 0` complementary to `ker P`, `U p.succ = A p '' U p.castSucc`,
>   `U last = range P`, each `U j` disjoint from the kernel of the suffix
>   `V j -> V last`, and all `U j` have `finrank K (range P)`.
> - **Orientation.** This Lean chain is source-to-target. It is Aoyagi's
>   notation after reversing the paper-order maps
>   `A^(s) : V_(s+1) -> V_s`.
> - **Proved.** The elementary subspace transport theorem, plus the adjacent
>   restricted-edge equivalence
>   `DLNFibre.DLN.Aoyagi.throughSubspaceEdgeEquiv` with apply lemma
>   `throughSubspaceEdgeEquiv_apply`.
> - **Assumed.** A field and vector spaces. No finite-dimensional hypothesis is
>   needed for the Lean helper; Aoyagi's matrix use case is finite-dimensional.
> - **Cited.** None.
> - **Deferred.** Packaging simultaneous chain bases; proving total-product
>   block form; connecting this subspace layer to the chart-local
>   product-reduction identity; full Aoyagi Theorem 3; and every analytic/RLCT
>   consequence.
> - **Kill conditions.** This is not a fixed-coordinate chart theorem. It does
>   not say arbitrary bases give identity top-left blocks; identity blocks
>   require transported bases on the through-subspaces.
