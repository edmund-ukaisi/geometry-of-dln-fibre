# Review - Lemma 5 equation (4) selected-span branch values

Reviewers: xhigh `Copernicus` source/indexing scout and xhigh `Beauvoir`
Lean/API scout.

Status: passed.

## Scope

This review covers:

```text
AoyagiSelectedCutpoints.block_leftEndpoint_lt_of_ne
AoyagiSelectedCutpoints.leftEndpoint_lt_of_lt_block
AoyagiLemma5Eq4SelectedSpanBranchValue
aoyagiLemma5Eq4_branchValue_of_block
aoyagiLemma5Eq4_selectedSpan_branchValue
```

The intended claim is only: given a supplied equation `(4)` piecewise
certificate, every point in the selected span has one of the advertised branch
values.

## Findings

No blocking findings.

The zero-based branch split matches Aoyagi's equation `(4)` after writing
`c=ell-a`, `r=p+c+1`, and `q=S_(p+c+2)-1`:

```text
b = 0                  first branch
1 <= b <= p            prefix branch
p < b <= p+c           middle branch
S = q                  boundary singleton
r <= b and q < S       tail branch
```

The off-by-one checks are correct.  The boundary point `q` is excluded from
the middle block because blocks are right-open.  It is the left endpoint of
block `r` only when `r<ell`; when `r=ell`, it is the terminal selected endpoint
and is outside the selected span.  The strict tail hypothesis `q<S` is
therefore necessary and correctly preserved.

The selected-span theorem is appropriately factored through a block-level
classifier.  It does not require the repaired cutoff guard as a Lean
precondition because it is conditional on the supplied certificate and uses the
total `point` accessor.  The source notes still record that the repaired guard
`p+1<=a` is needed for a source-faithful displayed-index interpretation.

## Verification

Controller ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
lake build DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector
git diff --check
```
