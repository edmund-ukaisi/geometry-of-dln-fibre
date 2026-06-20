# Statement card - A5 Lemma 5 equation (3) local data and label bridge

## Lean Artifacts

Files:

- `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- `lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_localData_of_widthGuards`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeUpperNat_one_add_one_labelBounds_of_sourceSelectedInequality_and_slack`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_localData_of_sourceSelectedInequality_and_slack`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_actualWidthLabel_of_widthCompatibility`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_actualWidthLabel_of_sourceSelectedInequality_and_slack`

## Statement

Lean now packages the safe local arithmetic for Aoyagi Lemma 5 equation `(3)`.
Under `1<=a`, `a<ell`, and the explicit width guards

```text
M-1 <= W_1+W_2,
W_1+2 <= M,
```

the special cutoff `S_(ell-a+2)` is a selected index, the first upper/lower
Htilde gap is one, and the label `k=Htilde'_1+1` is bounded by the selected
width `W_2`.

There is also a source-shaped version: Definition 3 supplies
`M-1<=W_1+W_2`, while the missing slack `W_1+2<=M` remains explicit.

Finally, the selected label bounds are bridged to `actualWidthLabel` under
explicit source-layer range, selected-width/actual-width compatibility, and
Nat/Int label compatibility.

## Proved

- Equation `(3)` local index, gap, and selected-label bounds under explicit
  width guards.
- Definition 3 plus `W_1+2<=M` gives the equation `(3)` selected-label bounds.
- The equation `(3)` selected label becomes an actual source label under
  actual-width compatibility.

## Assumed

- `1<=a` and `a<ell`.
- For the source-shaped theorem: Definition 3's selected-sum identity and
  strict selected-width inequalities.
- The extra one-unit slack `W_1+2<=M`.
- Actual source-layer range and actual-width compatibility for the
  `actualWidthLabel` bridge.

## Cited

- None in Lean. These are finite arithmetic and bookkeeping facts.

## Deferred

- Equation `(3)` displayed-vector construction or existence.
- Label legality from Definition 3 alone.
- Introduced-label status.
- Terminal `tilde t=0`.
- Source vector-to-chain correspondence, vector admissibility, Case 1(2) chart
  sequence, Lemma 5 order count, pole order, normal crossings, and RLCT
  extraction.

## Review

- Source/math audit: xhigh `Socrates`, which found a concrete Definition 3
  counterexample to equation `(3)` label legality without the slack.
- Lean API scout: xhigh `Faraday`, which recommended the actual-width bridge
  shape.
- Landed-patch review passed:
  `review-lemma5-eq3-local-data-and-piecewise-a5.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- `lake build DLNFibre.DLN.Aoyagi.HtildeChainArithmetic`
- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`
