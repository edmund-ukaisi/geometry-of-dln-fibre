# Review - A2 Case 2 endpoint equivalences from cardinalities

Date: 2026-06-28.

Reviewer: xhigh `James`.

Verdict: PASS.

## Checks

- `case2EndpointTransportEquivs_of_card_eq` is correctly scoped as
  noncanonical finite transport only: it assumes cardinality equalities and
  returns equivalences via `Fintype.equivOfCardEq`, with an explicit nonclaim
  docstring about labels, selected entries, Jacobians, and RLCT.
- `endpointComplementIndex_card_eq_H_rev_sub_rank` is mathematically honest:
  it rewrites the existing complement-cardinality lemma, uses
  `dimensionConvention q.rev`, and uses only the product-rank component of
  `sourceData.localSourceCertificate.source_basepoint`.
- No import-cycle or scope issue was found.  `Case2ResidualFactorProduct`
  imports `RegularSuspensionCoordinates`, while the source-data theorem stays
  inside `RegularSuspensionCoordinates` under
  `PaperEndpointFixedBaseRegularCoordinateSourceData`; no reverse Case 2
  dependency is introduced.
- The statement card and reproduction accurately separate proved finite
  cardinality/reindexing facts from deferred canonical, chart, Jacobian,
  pole-order, and RLCT claims.

Read-only verification by the reviewer:

```text
lake env lean DLNFibre/DLN/Aoyagi/Case2ResidualFactorProduct.lean
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
git diff --check -- <two Lean files>
```

All passed with no diagnostics.
