# Review - A4 Case 2 branch-indexed current-center payloads

Date: 2026-07-02.

Status: xhigh read-only source/API review, passed with hardening.

Reviewed target:
`statement-card-a4-case2-branch-indexed-current-center-payloads.md`.

## Source Audit

`Godel` rechecked Aoyagi pp. 19-22 and the existing A4 notes.  Verdict:
Aoyagi supports branch-dependent local selected-pivot charts, not a
recurrence-wide fixed-center all-pivot producer.

The source calculation is local at `(S,J)`: blow up the current residual block,
choose the displayed pivot chart, substitute `b'_i = u b_i`, apply regular
`Q/P`, transport `C'_J = Q^-1 C_J`, clear to `D'''_J`, and then continue with
`J` increased or advance `S`.  It does not define global chart tokens,
analytic source domains, recurrence-wide center alignment, produced
successor/suffix data, or one fixed atlas context as `(S,J)` varies.

The strongest honest contract is current-center local: for each active Case 2
state `s = (S,J)`, the natural center is
`case2ResidualBlockPivotEntries n S J`.  A recurrence-wide fixed-center
producer needs explicit alignment or a dependent branch-indexed atlas
interface.

## Lean/API Audit

`Poincare` confirmed the structural issue in Lean.  `SelectedEntryProducedBranchPayload`
and `SelectedEntryAtlasProducedBranchData` are both over one fixed `ctx`.
The new payload constructors return payloads over the current center
`case2ResidualBlockPivotEntries n s.S s.J`; a continuing edge increments `J`,
so the current center changes.

The requested hardening was to add a finite center-change theorem, not merely
a prose warning.  The theorem should avoid the overclaim "no producer exists";
the record could always be supplied by other means.  The true obstruction is
only to deriving recurrence-wide current-center payloads without alignment,
transport, or a dependent branch-indexed atlas.

## Verdict

Pass, provided the Lean slice includes:

- a named current-center function;
- a named fixed-center alignment predicate/record;
- a finite theorem that `case2ResidualBlockPivotEntries n S J` differs from
  `case2ResidualBlockPivotEntries n S (J+1)` under the Case 2 continuation
  bound;
- a no-parent-and-child alignment theorem for a continuing same-stage child;
- no conversion into `SelectedEntryAtlasProducedBranchData`.

## Nonclaims

No full producer, no total row-exhausted semantic payload, no analytic
coverage, no transition regularity, no Jacobian/volume compatibility, no
normal crossings, no pole order, and no RLCT extraction are reviewed or
claimed here.
