# Review - Lemma 5 Eq5 alpha-indexed branch cardinal bound

Reviewer: xhigh `Arendt`.

Scope:

- `aoyagiLemma5Eq5_alphaIndexedBranchLabelImage_card_le_actualWidthLabelFinset_card`;
- `aoyagiLemma5Eq5_alphaIndexedBranch_card_le_actualWidthLabelFinset_card`;
- reproduction and statement-card artifacts for the branch cardinal-bound slice.

## Findings

None.

## Verdict

Pass.  The two theorems stay within the supplied subset/cardinality boundary.
The image-card theorem applies `Finset.card_le_card` to the existing image
subset.  The branch-card theorem uses the existing image-card equality derived
from supplied `Set.InjOn alphaOf` and the displayed label formula, then applies
the image-card bound.

The patch does not overclaim branch construction, alpha-domain coverage,
terminal exactness, or coverage of actual-width labels.

## Commands Run

- `cd lean && lake build DLNFibre.DLN.Aoyagi.Lemma5SourceLabel`
- `git diff --check` on the scoped Lean/artifact files
- local `rg`/`sed` inspections of the Lean APIs and artifact text

## Residual Risk

The review was limited to this finite image/cardinality wrapper.  It did not
re-audit the upstream branchwise label theorem, alpha-domain arithmetic, or the
source-to-Lean correspondence beyond this boundary.
