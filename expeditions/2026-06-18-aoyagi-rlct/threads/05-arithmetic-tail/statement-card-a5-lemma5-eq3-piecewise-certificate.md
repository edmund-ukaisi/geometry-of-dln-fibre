# Statement card - A5 Lemma 5 equation (3) piecewise certificate

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`

Names:

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5Eq3PiecewiseSourceVector`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5Eq3SelectedSpanBranchValue`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_branchValue_of_block`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_selectedSpan_branchValue`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_piecewise_ownCoordinate_of_sourceSelectedInequality_and_slack`

## Statement

Lean now has a supplied branch certificate for Aoyagi Lemma 5 equation `(3)`.
If selected cutpoints, the guards `a<=ell` and `1<=a`, and a function `T` are
supplied with the displayed branch values, Lean classifies each source index
in the half-open selected span

```text
S_1-1 <= S < S_(ell+1)-1
```

into one of the advertised equation `(3)` branches.  The boundary point
`S_(ell-a+2)-1` remains separate from the strict tail branch.

Under `1<=a`, `a<ell`, Definition 3 selected-width hypotheses, and the extra
slack `W_1+2<=M`, the supplied piecewise certificate also gives the
own-coordinate value

```text
T(S_2-1) = Htilde'_1
```

together with the selected label bounds for `k=Htilde'_1+1`.

## Proved

- Supplied equation `(3)` branch record.
- Selected-block and selected-span branch classifiers.
- Own-coordinate and selected-label handoff under explicit slack.

## Assumed

- The supplied equation `(3)` branch certificate.
- The branch certificate includes `a<=ell` and `1<=a`, so the displayed
  boundary cutpoint is source-selected rather than totalized.
- For own-coordinate and selected-label handoff: `1<=a`, `a<ell`, Definition
  3 selected-width hypotheses, and `W_1+2<=M`.

## Cited

- None in Lean.  These are finite branch-bookkeeping and arithmetic facts.

## Deferred

- Construction or existence of the equation `(3)` displayed vector.
- Label legality from Definition 3 alone.
- Terminal `tilde t=0`, especially at the `a=1` boundary.
- Introduced-label status, source vector-to-chain correspondence, vector
  admissibility, Case 1(2) chart sequence, Lemma 5 order count, pole order,
  normal crossings, and RLCT extraction.

## Review

- Source/API audit: xhigh `Chandrasekhar`.
- Landed-patch review passed after adding guard fields:
  `review-lemma5-eq3-local-data-and-piecewise-a5.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`
