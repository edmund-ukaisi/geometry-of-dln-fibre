# Review - A5 Lemma 5 equation (4) own-coordinate sanity

Reviewer: xhigh `Hegel`.

Scope:

- `aoyagiHtildeUpperChain_sub_index_eq_lowerChain_of_le_min`;
- `aoyagiHtildeUpperNat_sub_index_eq_lowerNat_of_le_min`;
- reproduction, blocked audit, statement card, and ledger updates.

## Findings

None.

## Verdict

Pass as-is.

The Lean theorem is correctly scoped to the finite chain identity
`Htilde'_p - p = Htilde_p` under the explicit overlap assumptions `p<=a` and
`p<=ell-a`.  These assumptions force the already-formalised interval excess to
be exactly `p`.

No source-family overclaim was found.  The patch does not assert legal source
labels, terminality, vector admissibility, the Lemma 5 order count, normal
crossings, or RLCT extraction.  The blocked audit keeps the equation `(3)` and
`(4)` source-family realisation blockers visible.

## Commands Run

- `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- `./lean/scripts/sorries`
- `git diff --check`
