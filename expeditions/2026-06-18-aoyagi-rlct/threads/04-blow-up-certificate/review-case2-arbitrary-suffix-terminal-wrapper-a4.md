# Review - A4 Case 2 arbitrary-suffix terminal wrapper

Reviewed objects:

- `exists_sourceOldTopSuffix_entryIdeal_eq_sourceTerminalProduct_of_not_next_cont`
- `exists_sourceOldTopSuffix_entryIdeal_eq_suppliedTerminalCprimeProduct_of_not_next_cont`
- `exists_oldTopSuffix_entryIdeal_eq_relabelSuppliedTerminalProduct_of_actualWidth`
- `exists_oldTopSuffix_entryIdeal_eq_relabelOriginalRowsTerminalProduct_of_actualWidth`
- `reproduction-case2-arbitrary-suffix-terminal-wrapper-a4.md`
- `statement-card-a4-case2-arbitrary-suffix-terminal-wrapper.md`

Verdict: no blocking source/math or Lean API issue found.

The slice matches the stopped Case 2 terminal passage and the previous
source-suffix/row-exhausted reviews.  The arbitrary following matrix is typed
as `F : Matrix τ υ R`: its row/input type `τ` matches the terminal factor's
output columns, while its output column type `υ` is arbitrary.  The
actual-width wrappers require `n(S+1)=J+1`; the row-exhausted transported
branch remains separate.

## Nonblocking Suggestions Applied

- The reproduction now describes `F` as `Matrix τ υ R`, rather than saying it
  has the same column type as the following factor.
- The statement card now records the same composability boundary.

## Caveats

- `F` is supplied, not produced.
- The supplied terminal bridge is consumed, not chart-produced.
- Actual-width original rows do not follow from row exhaustion.
- No chart coverage, normal-crossing/RLCT, transition invariant, or
  source-produced `C'^(S+1)` theorem is proved.
