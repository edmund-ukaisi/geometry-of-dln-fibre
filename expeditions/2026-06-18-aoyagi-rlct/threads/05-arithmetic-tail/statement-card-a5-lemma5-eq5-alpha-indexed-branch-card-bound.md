# Statement card - A5 Lemma 5 Eq5 alpha-indexed branch cardinal bound

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_alphaIndexedBranchLabelImage_card_le_actualWidthLabelFinset_card`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_alphaIndexedBranch_card_le_actualWidthLabelFinset_card`

## Claim

For a supplied finite Eq5 strict-offset branch family, if each supplied branch
label is legal by the branchwise alpha-indexed source-label hypotheses, then

```text
(branches.image branchLabel).card <= (actualWidthLabelFinset L n).card.
```

If the supplied alpha projection is injective on the branch family, then also

```text
branches.card <= (actualWidthLabelFinset L n).card.
```

## Proved

The theorems combine:

- the previous subset
  `branches.image branchLabel <= actualWidthLabelFinset L n`;
- the previous image-cardinality equality
  `(branches.image branchLabel).card = branches.card`, only for the branch
  cardinality bound.

## Assumed

The branch family, alpha map, branch-label map, branchwise alpha-domain
membership, source range, width bound, displayed label formula, and alpha
injectivity are all supplied explicitly.

## Deferred

Branch construction, alpha-domain coverage, selected-span coverage, displayed
vector construction, terminal exactness, classifier/back-to-label coverage,
Lemma 5 order count, pole order, normal crossings, and RLCT extraction.

## Review

xhigh `Arendt` passed with no findings.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.Lemma5SourceLabel`
