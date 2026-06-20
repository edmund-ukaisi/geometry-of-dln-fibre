# Statement card - A5 Lemma 5 equation (4) selected-span branch values

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`

Names:

- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.block_leftEndpoint_lt_of_ne`
- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.leftEndpoint_lt_of_lt_block`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5Eq4SelectedSpanBranchValue`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_branchValue_of_block`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_selectedSpan_branchValue`

## Statement

Given selected cutpoints and a supplied Aoyagi Lemma 5 equation `(4)`
piecewise certificate for a function `T`, Lean classifies every source index in
the selected span

```text
S_1-1 <= S < S_(ell+1)-1
```

by one of the advertised branch values: first, prefix, middle, boundary, or
tail.

## Proved

- Two endpoint-ordering helpers for half-open selected blocks.
- A branch-value inductive recording the five equation `(4)` alternatives.
- A block-level branch classifier.
- A selected-span classifier obtained from selected-span block coverage.

## Assumed

- Selected cutpoints and their strict order.
- The supplied equation `(4)` piecewise branch certificate.

## Cited

- None in Lean.  This is finite selected-block bookkeeping and supplied branch
  data.

## Deferred

- Construction/existence of the displayed vector.
- Source-layer coverage outside the selected span or at `S_(ell+1)-1`.
- Terminal `tilde t=0`, vector admissibility, source vector-to-chain
  correspondence, Case 1(2) chart sequence, Lemma 5 order count, pole order,
  normal crossings, and RLCT extraction.

## Review

- Source/indexing scout: xhigh `Copernicus`.
- Lean/API scout: xhigh `Beauvoir`.
- Review artifact:
  `review-lemma5-eq4-selected-span-branch-value-a5.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`
- `lake build DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector`
- `git diff --check`
