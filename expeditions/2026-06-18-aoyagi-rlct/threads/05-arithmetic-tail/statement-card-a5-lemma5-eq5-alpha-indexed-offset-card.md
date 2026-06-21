# Statement card - A5 Lemma 5 Eq5 alpha-indexed offset cardinality

## Lean Name

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_alphaIndexedBranchLabelImage_card_eq_offsetValueSet_card`

## Claim

For a supplied finite Eq5 strict-offset branch family, if the supplied alpha
projection covers the strict Eq5 alpha domain and is injective on the branch
family, then the supplied branch-label image has the same cardinality as the
strict Eq5 offset-value set:

```text
(branches.image branchLabel).card =
  (aoyagiLemma5Eq5OffsetValueSet ell a p M m).card.
```

## Proved

Both sides are counted through `aoyagiLemma5Eq5AlphaDomain ell a p`.  The
branch-label side uses supplied alpha injectivity and the displayed label
formula.  The offset-value side uses injectivity of
`alpha |-> Htilde'_p - alpha` and the existing offset-value image theorem.

## Assumed

The branch family, alpha map, branch-label map, alpha-domain coverage,
alpha-projection injectivity, and displayed label formula are all supplied
explicitly.

## Deferred

Branch construction, source-label legality, width compatibility, set equality
or an explicit bijection between branch labels and offset values, coverage of
actual-width labels or terminal-minimum labels, pole order, normal crossings,
and RLCT extraction.

## Review

xhigh `Huygens` passed the proposed theorem with no blocking findings.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.Lemma5SourceLabel`
