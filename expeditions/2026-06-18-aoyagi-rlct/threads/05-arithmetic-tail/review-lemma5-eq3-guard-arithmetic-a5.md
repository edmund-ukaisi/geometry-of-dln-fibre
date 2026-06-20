# Review - A5 Lemma 5 equation (3) guard arithmetic

Reviewer: xhigh `Turing`.

Scope:

- `aoyagiLemma5Eq3_selectedIndexGuard_iff`;
- `aoyagiHtildeUpperNat_one_sub_lowerNat_one_of_pos_of_lt`;
- `aoyagiHtildeUpperNat_one_add_one_labelBounds_iff_widthGuards`;
- reproduction, statement card, and ledger updates.

## Findings

None.

## Verdict

Pass as-is.

The selected-index guard correctly proves
`ell-a+2<=ell+1 <-> 1<=a` under `a<=ell`.  The first-gap theorem correctly
reduces the upper/lower Htilde gap at `1` to interval excess `1` under
`1<=a` and `a<ell`.  The label-bounds theorem correctly rewrites
`1<=Htilde'_1+1<=W_2` as `M-1<=W_1+W_2` and `W_1+2<=M`.

No source overclaim was found.  The patch keeps equation `(3)` vector
construction, legal labels from Definition 3 alone, terminal `tilde t=0`,
Lemma 5 order count, and RLCT extraction blocked.

## Commands Run

- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean`
- `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- `git diff --check`
- touched-file scan for `sorry`, `axiom`, `native_decide`, and `#exit`
