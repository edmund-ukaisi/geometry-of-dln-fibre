# Review - Case 2 constructed old-top `Cprime` terminal prefix

Date: 2026-06-24.

Reviewer: xhigh checker `Ramanujan the 2nd`.

## Verdict

Accept after corrections.  The corrections were incorporated before Lean work.

The slice is source-safe as finite bookkeeping.  Aoyagi pp. 21-22 support the
stopped Case 2 terminal-prefix display with `C'^(S+1)` indexed by terminal
prefix rows `1..M(S+1)` and the transported factor
`C'_J^(S+1)=Q^-1 C_J^(S+1)`.  The Lean claim only reindexes the already
constructed `[Cold; top(Cprime)]` source-row terminal matrix along
`case2SourceTerminalRowEquivPrefixOfNotNext`.

## Corrections Applied

- Replaced informal `~=` notation with Lean's `≃`.
- Clarified that the direct source-row equality is obtained by
  `SuppliedTerminalCprimeBridge.of_constructedWithOldTopFromCprime` plus
  `SuppliedTerminalCprimeBridge.cprimeCandidate_eq`; the previous
  terminal-row theorem gives the reindexed block form.
- Added explicit types for `Cold`, `Cprime`, `Wold`, `b0`, and `F`, including
  `[Fintype tau]` for the product theorem.
- Tightened the source anchor: Aoyagi gives the terminal-prefix display, while
  source-row and arbitrary free-`Cprime` packaging is repo finite algebra
  motivated by that display.

## Boundary Check

- `hstop : not (J+2 <= prefixMinNat n (S+1))` is essential.  Together with
  `hcont`, it gives the stopped-prefix row equivalence.
- No actual-width collapse is used.  Replacing the transported pivot row by the
  original source row still requires the separate hypothesis `n(S+1)=J+1`.
- In row-exhausted wide-next cases, row `J+1` remains `top(Q^-1 C)`, here
  `top(Cprime)`.
- The terminal-prefix row count is `J+1`; this is prefix width, not actual next
  width.

## Nonclaims

No chart/source production, no terminal data production, no suffix production,
no transition regularity, no chart coverage, no normal crossings, no pole
order, no termination theorem, and no RLCT consequence.
