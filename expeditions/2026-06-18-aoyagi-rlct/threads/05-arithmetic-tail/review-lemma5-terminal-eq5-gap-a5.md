# Review - Lemma 5 terminal Eq5 gap

Date: 2026-06-21.

Reviewer: Aquinas, xhigh-effort read-only review.

Verdict: ACCEPT.

## Scope

Reviewed the terminal Eq5 gap slice:

- `aoyagiLemma5Eq5OffsetValueSet_eq_empty_of_terminal`
- `aoyagiHtildeIntervalValueSetNat_terminal_eq_singleton_zero_of_selectedSum`
- `aoyagiLemma5Eq5_terminal_offsets_ne_intervalValueSetNat_of_selectedSum`
- `aoyagiLemma5_suppliedTerminalZero_Eq5_offsets_eq_intervalValueSetNat`
- `aoyagiLemma5_suppliedTerminalUpper_Eq5_offsets_eq_intervalValueSetNat`

The review checked the Lean proof, reproduction, statement card, and
expedition ledger/thread/synthesis/claims/priorities updates.

## Findings

No blocking findings.

The terminal Eq5-offset theorem is sound: at `p=ell`, the interval excess has
the factor `ell-ell=0`, so no strict positive offset exists.  The terminal
interval singleton theorem keeps both `a<=ell` and the selected-width sum
explicit and uses the existing terminal-zero facts for the lower and upper
Htilde chains.

The noncoverage theorem and supplied coverage wrappers are narrow.  Eq5
offsets alone do not fill `{0}`; a separately supplied terminal zero fills it;
and the terminal-upper wrapper is only the same supplied endpoint statement
after rewriting `Htilde'_ell=0` under the selected-width sum.

The docs correctly mark terminal zero and terminal upper as supplied
bookkeeping, not source construction, terminal-label exactness, or Lemma 5
completion.

## Verification

The reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
git diff --check
```

Both passed.  The reviewer also scanned the touched Lean file for `sorry`,
`axiom`, `native_decide`, `#exit`, and `unsafe`; no matches were found.
