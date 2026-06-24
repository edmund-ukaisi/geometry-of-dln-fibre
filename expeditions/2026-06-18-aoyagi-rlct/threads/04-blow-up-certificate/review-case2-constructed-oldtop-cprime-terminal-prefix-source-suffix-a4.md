# Review - Case 2 constructed old-top `Cprime` terminal-prefix source suffix

Date: 2026-06-24.

Reviewer: xhigh checker `Lorentz the 2nd`.

## Verdict

Accepted after one wording correction, which was incorporated before Lean
work.

The target is source-safe finite bookkeeping.  It specializes the existing
supplied-terminal-prefix entry-ideal consumer using
`SuppliedTerminalCprimeBridge.of_constructedWithOldTopFromCprime`.

## Correction Applied

The reproduction now says that the transported terminal source-row matrix is
the source-row reindexing of `[Cold; top(Cprime)]`, not literally the raw block.
The terminal-prefix side is then the further reindexing by
`case2SourceTerminalRowEquivPrefixOfNotNext ... hstop`.

## Boundary Check

- The terminal side must use the double reindexing of `[Cold; top(Cprime)]`.
  It is not `[Cold; Cprime]` and not original source rows.
- The source side uses `[Cold; Q*Cprime]`, i.e.
  `verticalBlock Cold
  (case2DisplayedPaperConstructedFollowingFactor ... Cprime)`.
- `sourceSuffixProduct kappa Ctail S hSuffix` remains a supplied raw suffix.
- `hstop` is essential; no actual-width hypothesis `n(S+1)=J+1` is assumed.

## Nonclaims

No source production of `Csucc` or `C'^(S+1)`, no successor chart production,
no chart coverage, no transition regularity, no normal crossings, no pole
order, no termination theorem, and no RLCT consequence.
