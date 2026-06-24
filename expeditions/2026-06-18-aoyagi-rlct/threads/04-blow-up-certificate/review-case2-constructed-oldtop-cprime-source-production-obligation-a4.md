# Review - Case 2 constructed old-top `Cprime` source-production obligation

Date: 2026-06-24.

Reviewer: xhigh checker `Hegel the 2nd`.

## Verdict

Accepted with two statement-hygiene corrections, both incorporated before Lean
formalisation.

The reproduction is source-safe: it packages the constructed old-top/free
`Cprime` following factor into `SourceProductionObligation` by transporting
the canonical formula-level obligation along the constructed terminal-row
equality.  It does not claim source production.

## Corrections Applied

- The source suffix setup now includes the Lean typeclass assumptions
  `[forall i, Fintype (kappa i)]` and `[forall i, DecidableEq (kappa i)]`.
- The intended unreindexed terminal-row equality is stated with right-hand side
  equal to the source-row reindexing of `[Cold; top(Cprime)]`, namely
  `(verticalBlock Cold top(Cprime)).submatrix (case2SourceTerminalRowEquiv J).symm id`,
  not the raw stacked matrix.

## Boundary Check

- The terminal matrix is the source-row reindexing of `[Cold; top(Cprime)]`.
  It is not `[Cold; Cprime]`.
- The pivot terminal row is not replaced by an original source row unless a
  separate actual-width hypothesis is present.
- The theorem has no outer stopped-continuation, actual-width, or
  row-exhaustion hypothesis; those branch hypotheses occur only inside the
  generic obligation fields.
- The proof should reuse
  `SourceProductionObligation.of_formulaSuccessor_transportTerminalRows` and
  the existing constructed terminal-row reindexing lemma.

## Nonclaims

No source production of `Csucc` or `C'^(S+1)`, no suffix construction, no
successor chart construction, no chart coverage, no transition regularity, no
normal crossings, no pole order, no termination theorem, and no RLCT
consequence.
