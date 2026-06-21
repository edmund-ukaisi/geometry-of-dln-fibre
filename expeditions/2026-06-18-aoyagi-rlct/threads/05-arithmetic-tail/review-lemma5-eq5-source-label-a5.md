# Review - Lemma 5 equation (5) source label

Reviewer: `Peirce` (xhigh).  Verdict: no blocking mathematical or
source-fidelity findings.

## Findings

No blocking issues were found, provided the theorem keeps the explicit bridge
hypotheses used in the landed statement.

Non-blocking statement/API checks:

- `actualWidthLabel` requires source-layer range data:
  `1 <= C.point p - 1` and `C.point p - 1 <= L`.  These remain explicit,
  matching the equation `(4)` actual-label bridge pattern.
- The natural label is supplied through the integer equality
  `(k : Z) = Htilde'_p + 1 - alpha`, avoiding any claim that the displayed
  integer expression is definitionally a natural number.
- The source guard `alpha<p` is faithful to equation `(5)` but is not needed
  for the bare label-bound arithmetic.  The label bounds use only
  `1<=alpha` and `alpha<=aoyagiLemma5IntervalExcess ell a p`.
- The theorem keeps `p<=ell` explicit.  This is harmless and simpler than
  deriving it from the interval-excess guard.
- The own-coordinate wrapper uses `C.point p - 1`.  A theorem for arbitrary
  `s` in `C.block p s` would need actual-width compatibility at that `s`, not
  only at the block's left endpoint.

## Source Fidelity

Paper `j0` is Lean coordinate `p`.  The own block is paper
`j=j0+1`, represented by `C.block p`.  The source-label relation is

```text
k = Htilde'_p + 1 - alpha.
```

Definition 3 supplies the selected-width inequalities needed for both bounds

```text
1 <= k <= W_(p+1).
```

The Lean arithmetic theorem
`aoyagiLemma5Eq5_labelBounds_of_sourceSelectedInequality` proves this under
the stated alpha/excess and selected-width hypotheses.

## Checks

The reviewer reported:

```text
lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean
lake env lean DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean
lake build DLNFibre.DLN.Aoyagi.Lemma5SourceLabel
git diff --check
```

The focused Lean checks and module build passed.  The diff check passed.  A
forbidden-token scan found no `sorry`, `axiom`, `native_decide`, or `#exit`.

## Residual Risks

The following remain outside this theorem:

- construction or existence of equation `(5)`'s displayed vector;
- terminal `tilde t=0`;
- arbitrary-point source-label legality inside the whole block;
- vector admissibility and source-vector-to-chain correspondence;
- Case 1(2) chart sequence;
- Lemma 5 order count;
- pole order, normal crossings, or RLCT extraction.
