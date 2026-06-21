# Statement card - A5 Lemma 5 Eq5 alpha-indexed branch-label image

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_alphaIndexedBranchLabelImage_subset_actualWidthLabelFinset_of_widthBound`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_alphaIndexedBranchLabelImage_card_eq_of_alphaInj`

## Claim

For a supplied finite Eq5 strict-offset branch family, if each supplied branch
label is legal by the branchwise alpha-indexed source-label hypotheses, then
the finite branch-label image is contained in `actualWidthLabelFinset L n`.

If the supplied alpha projection is injective on the branch family, then the
branch-label image has the same cardinality as the supplied branch family.

## Proved

- Image-level subset:
  `branches.image branchLabel <= actualWidthLabelFinset L n`.
- Image cardinality under supplied alpha injectivity:
  `(branches.image branchLabel).card = branches.card`.

## Assumed

The branch family, alpha map, branch-label map, branchwise alpha-domain
membership, source range, width bound, displayed label formula, and alpha
injectivity are all supplied explicitly.

## Deferred

Branch construction, alpha-domain coverage, selected-span coverage, displayed
vector construction, terminal exactness, classifier/back-to-label coverage,
Lemma 5 order count, pole order, normal crossings, and RLCT extraction.

## Review

Landed-patch review passed by xhigh `Linnaeus`.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.Lemma5SourceLabel`
