# Review - Lemma 5 equation (5) piecewise certificate

Reviewer: `Aristotle` (xhigh).  Verdict: one low documentation finding,
fixed.

## Finding

- Low: the module doc in `Lemma5DisplayedVector.lean` still said the file
  introduced supplied certificates only for equations `(3)` and `(4)`, while
  this slice adds equation `(5)`.  The Lean statements were sound.  The module
  doc now says `(3)`, `(4)`, and `(5)`.

## Source Fidelity

No source-fidelity finding remained after review.  The branch translation
matches Aoyagi PDF p. 27, equation `(5)`:

```text
paper j = Lean b+1,
paper j0 = Lean p.
```

The alpha guards and post-`p` branch are shifted correctly, and the final
cutoff is represented by the explicit guard

```text
p+(a-alpha)+1 <= ell.
```

When `alpha=1`, the printed row `alpha<=j<=j0` can syntactically overlap the
first row at `j=1`.  Lean resolves selected-span classification by routing
block `b=0` through `first` and requiring `1<=b` for later selected-block
rows.  This is a classifier convention, not a construction or disjointness
claim.

## Checks

The reviewer ran:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
rg 'sorry|axiom|native_decide|#exit' lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
```

The focused Lean check passed, and the forbidden-token scan found no matches.
The reviewer also checked the two new Eq5 docs for trailing whitespace and ran
`git diff --check` on reviewed files; no issues were found.

## Residual Risks

The following remain correctly outside the theorem:

- construction or existence of equation `(5)`'s displayed vector;
- source-label legality for `k`;
- terminal `tilde t=0`;
- chart sequence and chart coverage;
- vector admissibility;
- Lemma 5 order count;
- pole order, normal crossings, or RLCT extraction.
