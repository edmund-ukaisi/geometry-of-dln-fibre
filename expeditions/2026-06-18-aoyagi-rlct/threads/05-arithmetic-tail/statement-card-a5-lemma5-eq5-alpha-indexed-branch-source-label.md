# Statement card - A5 Lemma 5 Eq5 alpha-indexed branch source label

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_alphaIndexedBranch_actualWidthLabel_of_widthBound`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_alphaIndexedBranchLabel_mem_actualWidthLabelFinset_of_widthBound`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_alphaIndexedBranchLabel_injOn`

## Claim

A supplied finite Eq5 strict-offset branch family has legal actual-width
source labels branchwise if each branch alpha lies in the strict Eq5 alpha
domain, each supplied source coordinate is in range, the selected width is
bounded by the actual width at that source coordinate, and the supplied label
is `Htilde'_p+1-alpha`.

If the supplied alpha projection is injective on the branch family, then the
supplied branch-label map is injective on that family.

## Proved

The source-label wrapper applies the existing alpha-family source-label theorem
to each branch.  The finite-set wrapper converts the resulting
`actualWidthLabel` statement to membership in `actualWidthLabelFinset`.  The
injectivity wrapper cancels the common `Htilde'_p+1` in the displayed label
formula and uses supplied alpha injectivity.

## Assumed

The branch family, alpha map, branch-label map, branchwise alpha-domain
membership, branchwise source range, branchwise width bound, and alpha
injectivity are all supplied explicitly.

## Deferred

Branch construction, alpha-domain coverage, selected-span coverage, displayed
vector construction, terminal exactness, classifier/back-to-label coverage,
Lemma 5 order count, pole order, normal crossings, and RLCT extraction.

## Review

xhigh reviewer `Peirce` passed after docstring scope repairs; scout `Herschel`
recommended this branch-label API shape and warned not to infer injectivity
from alpha-domain coverage alone.
