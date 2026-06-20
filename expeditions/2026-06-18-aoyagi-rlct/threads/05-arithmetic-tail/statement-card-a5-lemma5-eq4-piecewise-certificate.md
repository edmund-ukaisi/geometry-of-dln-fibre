# Statement card - A5 Lemma 5 equation (4) piecewise certificate

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`

Names:

- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints`
- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.point`
- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.block`
- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.leftEndpoint_mem_block`
- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.cut_strictMono`
- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.point_strict_of_lt`
- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.point_le_of_le`
- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.block_index_unique`
- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.block_leftEndpoint_iff`
- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.block_leftEndpoint_lt_of_ne`
- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.leftEndpoint_lt_of_lt_block`
- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.block_mem_selectedSpan`
- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.exists_block_of_mem_selectedSpan`
- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.exists_block_iff_mem_selectedSpan`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5Eq4PiecewiseSourceVector`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5Eq4SelectedSpanBranchValue`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_branchValue_of_block`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_selectedSpan_branchValue`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_piecewise_ownCoordinate_of_sourceSelectedInequality`

## Statement

Lean now has a conditional source-vector-facing certificate for Aoyagi Lemma 5
equation `(4)`.  If selected cutpoints are supplied and a function `T` is
certified to satisfy the displayed equation `(4)` branch values on selected
blocks, then under the repaired guards

```text
1<=p,     p+1<=a,     p<=ell-a,
```

and Definition 3's selected-width hypotheses, Lean proves:

```text
p + (ell-a) + 2 <= ell+1,
T(S_(p+1)-1) = Htilde_p,
1 <= Htilde_p+1 <= W_(p+1).
```

## Proved

- Basic selected-cutpoint and selected-block vocabulary.
- The left endpoint of a selected block belongs to that block.
- Selected cutpoint monotonicity, selected-block uniqueness, and uniqueness
  of a selected block's left endpoint.
- Selected-block coverage of exactly the selected span
  `S_1-1 <= S < S_(ell+1)-1`.
- A supplied equation `(4)` piecewise certificate gives one of the advertised
  branch values for every point in the selected span.
- A supplied equation `(4)` piecewise certificate gives the correct own
  coordinate.
- The same theorem carries forward the repaired selected-index and legal-label
  conclusions.

## Assumed

- The selected cutpoints and their strict order.
- The supplied equation `(4)` branch certificate.
- `1<=ell`, `a<=ell`, `1<=p`, `p+1<=a`, and `p<=ell-a`.
- The selected-width sum `sum W = ell*(M-1)+a`.
- The strict source selected inequality `ell*W_i < sum W`.

## Cited

- None in Lean.  This is finite arithmetic and supplied branch data from
  Aoyagi Lemma 5 equation `(4)`.

## Deferred

- Construction/existence of the displayed vector.
- Total source-layer coverage.
- Coverage outside the selected span `S_1-1 <= S < S_(ell+1)-1`.
- Terminal `tilde t=0`.
- Vector admissibility and source vector-to-chain correspondence.
- Compatibility between selected widths and actual layer widths, such as
  `m i = layerWidth(point C i)`, for future theorems that need it.
- Case 1(2) chart sequence.
- Lemma 5 chart-family coverage/order count, pole order, normal crossings,
  and RLCT extraction.

## Review

- Source scout: xhigh `Anscombe`.
- Lean/API scout: xhigh `Herschel`.
- Landed-patch review passed by xhigh `Singer`:
  `review-lemma5-eq4-piecewise-certificate-a5.md`.
- Selected-block coverage review passed by xhigh `Pauli`:
  `review-selected-block-coverage-a5.md`.
- Selected-span branch-value source/API review passed by xhigh `Copernicus`
  and xhigh `Beauvoir`:
  `review-lemma5-eq4-selected-span-branch-value-a5.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`
- `lake build DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector`
- `lake env lean DLNFibre.lean`
- `git diff --check`
- `./lean/scripts/sorries`
