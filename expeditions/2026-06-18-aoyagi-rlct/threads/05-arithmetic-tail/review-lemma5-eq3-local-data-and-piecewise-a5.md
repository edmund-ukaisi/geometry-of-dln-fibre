# Review - Lemma 5 equation (3) local data, actual label, and piecewise certificate

Reviewer: xhigh `Lagrange`.

Scope:

- `aoyagiLemma5Eq3_localData_of_widthGuards`;
- `aoyagiHtildeUpperNat_one_add_one_labelBounds_of_sourceSelectedInequality_and_slack`;
- `aoyagiLemma5Eq3_localData_of_sourceSelectedInequality_and_slack`;
- `aoyagiLemma5Eq3_actualWidthLabel_of_widthCompatibility`;
- `aoyagiLemma5Eq3_actualWidthLabel_of_sourceSelectedInequality_and_slack`;
- `AoyagiLemma5Eq3PiecewiseSourceVector`;
- `AoyagiLemma5Eq3SelectedSpanBranchValue`;
- `aoyagiLemma5Eq3_branchValue_of_block`;
- `aoyagiLemma5Eq3_selectedSpan_branchValue`;
- `aoyagiLemma5Eq3_piecewise_ownCoordinate_of_sourceSelectedInequality_and_slack`;
- reproduction, statement cards, and ledger updates.

## Findings

One API hygiene issue was found and addressed.

The initial `AoyagiLemma5Eq3PiecewiseSourceVector` record exposed the boundary
`C.point (ell-a+1)-1` for arbitrary `a`.  Since `C.point` is totalized outside
the selected range, the record needed explicit source-index guards to avoid
being read as source-valid without them.

Fix: the record now includes

```text
a_le_ell : a <= ell
indexGuard : 1 <= a
```

so any supplied equation `(3)` certificate carries the guards needed for the
boundary `S_(ell-a+2)` to be a selected source cutpoint.

## Verdict

Pass after the guard-field fix.

The zero-based branch translation matches Aoyagi PDF p. 27: `b=j-1`, upper
branch `1<=b<=ell-a`, special boundary `C.point (ell-a+1)-1`, and strict tail
after that boundary.  Definition 3 is used only for `M-1<=W_1+W_2`; the slack
`W_1+2<=M` remains explicit.  The actual-label bridge has the needed
source-layer range and actual-width compatibility hypotheses.

No terminal `tilde t=0`, introduced-label, vector-construction, chart-family,
or order-count overclaim was found.

## Commands Run

- `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`
- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`
- `lake build DLNFibre.DLN.Aoyagi.HtildeChainArithmetic DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector DLNFibre.DLN.Aoyagi.Lemma5SourceLabel`
- `git diff --check`
