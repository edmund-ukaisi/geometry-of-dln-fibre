# Statement card - A2 transformed-edge rank-stratum bridge

> **Claim.** For the fixed-base A2 product-reduction boundary, the exact rank
> condition on the transformed edge visited by the recursive Schur-residual
> suffix state is equivalent to the existing fixed-base edge-rank stratum.

- **Lean:**
  `DLNFibre.DLN.Aoyagi.paperEndpointFixedBase_transformedEdgeRanks_iff_edgeRankStratum`
  in `lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`.
- **Source anchor:** Aoyagi 2023, Lemma 2 and Theorem 3, PDF pp. 10-13.
- **Pen-and-paper check:** the transformed edge is
  `[I Bprev; 0 I] * E_p`; the left multiplier is determinant-unit
  block-unitriangular, so it preserves rank.  Hence transformed-edge rank
  equals the original source edge rank.
- **Proved:** a finite-dimensional rank-predicate equivalence between the
  recursive transformed-edge rank condition and
  `paperEndpointFixedBaseEdgeRankStratum`.
- **Assumed:** the fixed-base endpoint setup, finite-dimensional vector spaces,
  the chosen total-kernel complement `U0`, and the source edge family `Cedge`.
- **Cited:** none.
- **Deferred:** exact-rank openness, source-stratum nonemptiness, source chart
  production, analytic ideal transport, regular-suspension/RLCT additivity,
  normal-crossing production, pole order, and RLCT extraction.
- **Verification:** focused build
  `lean/scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionBoundary` passed;
  full build `lean/scripts/lb DLNFibre` passed; `lean/scripts/sorries`
  reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`; `git diff --check`
  passed.
- **Review:** xhigh read-only review passed with no blocking findings in
  `review-a2-transformed-edge-rank-stratum-bridge.md`.
