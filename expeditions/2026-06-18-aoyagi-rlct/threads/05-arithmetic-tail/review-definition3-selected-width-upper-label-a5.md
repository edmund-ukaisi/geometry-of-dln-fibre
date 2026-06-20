# Review - A5 Definition 3 selected-width upper label bound

Reviewer: xhigh `Bohr`.

Scope:

- `aoyagiSelectedWidth_le_pred_of_sourceSelectedInequality`;
- `aoyagiPrefixSum_sub_current_add_one_le_mul_of_selectedWidth_le_pred`;
- `aoyagiHtildeLowerNat_add_one_le_selectedWidth_of_selectedWidth_le_pred`;
- `aoyagiHtildeLowerNat_add_one_le_selectedWidth_of_sourceSelectedInequality`;
- reproduction, statement card, and ledger updates.

## Findings

None.

## Verdict

Pass as-is.

The Lean hypotheses match the intended Definition 3 slice: `ell>0`,
`a<=ell`, the selected-width sum identity, and the strict selected inequality.
The derivation `W_i<=M-1` is mathematically correct, and the prefix/label
wrappers prove only the upper equation `(4)` label inequality
`Htilde_p+1<=W_(p+1)`.

No source overclaim was found.  Lower positivity, terminality, equation `(3)`
slack, displayed-family realisation, Lemma 5 order count, and RLCT extraction
remain blocked.

## Commands Run

- `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- `git diff --check`
- added-diff scan for `sorry`, `axiom`, `native_decide`, and `#exit`
