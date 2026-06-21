# Review - Lemma 5 Eq5 alpha-indexed branch-label image

Reviewer: xhigh `Linnaeus`.

Scope:

- `aoyagiLemma5Eq5_alphaIndexedBranchLabelImage_subset_actualWidthLabelFinset_of_widthBound`;
- `aoyagiLemma5Eq5_alphaIndexedBranchLabelImage_card_eq_of_alphaInj`;
- reproduction/card/ledger updates for the branch-label image slice.

## Findings

None.

## Verdict

Pass.  The Lean additions stay within finite supplied-image bookkeeping: the
subset theorem only unpacks `branches.image branchLabel` and applies the
existing branchwise membership theorem, and the cardinality theorem only
applies `Finset.card_image_of_injOn` using supplied alpha injectivity.

The artifacts and ledger text preserve the same boundary: supplied branch
family, supplied alpha map/injectivity, subset/cardinality only, and explicit
nonclaims for construction, coverage, terminal exactness,
classifier/back-to-label, pole order, normal crossings, and RLCT.

## Commands Run

- `lake build DLNFibre.DLN.Aoyagi.Lemma5SourceLabel`
- `git diff --check`
- scoped scan for `sorry`, `axiom`, `native_decide`, and `#exit` in
  `Lemma5SourceLabel.lean`
- trailing-whitespace check on the new artifact files

## Residual Risk

The review was limited to this finite image/cardinality wrapper.  It did not
re-audit the upstream branchwise label theorem, alpha-domain arithmetic lemmas,
or the paper-to-Lean correspondence beyond this boundary.
