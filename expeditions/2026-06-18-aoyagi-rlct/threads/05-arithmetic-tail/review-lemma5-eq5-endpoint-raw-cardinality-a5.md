# Review - Lemma 5 Eq5 endpoint raw cardinality

Date: 2026-06-22.

Reviewer: Arendt, xhigh independent landed-slice review.

Scope:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5SuppliedCoverage.lean`
- `reproduction-lemma5-eq5-endpoint-raw-cardinality-a5.md`
- `statement-card-a5-lemma5-eq5-endpoint-raw-cardinality.md`

## Findings

Low: the statement-card verification command was initially cwd-ambiguous.  The
command passes from `lean/`, but fails from the worktree root.  The statement
card now states the working directory explicitly.

## Verdict

Pass.

The value-injective theorem correctly composes:

- raw value-image equality;
- `Finset.card_image_of_injOn`;
- Htilde interval value-set cardinality.

The alpha-injective theorem correctly delegates raw value injectivity to
`aoyagiLemma5Eq5EndpointRawBranches_value_injective_of_alpha_injective`.
Strict alpha injectivity remains supplied, so there is no hidden
source-construction claim.

## Nonclaims Checked

The slice is interior-coordinate only.  It does not claim `j=0` or terminal
cardinality, filtered nonbase survival, source branch construction,
source-label legality, terminal-minimum exactness, no-extra coverage, pole
order, normal crossings, or RLCT extraction.

## Verification Noted By Reviewer

- `cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5SuppliedCoverage.lean`
- focused placeholder scan found no `sorry`, `axiom`, `native_decide`, or
  `#exit` in the touched Lean file.
