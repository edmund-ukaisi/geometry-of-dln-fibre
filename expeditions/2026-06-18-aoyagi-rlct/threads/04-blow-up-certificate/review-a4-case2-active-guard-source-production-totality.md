# Review - A4 Case 2 active guards for source-production totality

Date: 2026-07-02.

Status: PASS after controller fixes.

## Scope

Review the guard refinement and finite source-data layer:

- `reproduction-a4-case2-active-guard-source-production-totality.md`;
- `statement-card-a4-case2-active-guard-source-production-totality.md`;
- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryCase2ProducedGuards.lean`;
- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotProducedSourceData.lean`;
- ledger updates that mention the active-refined guard decision.

## Controller Pre-Review Checklist

The refinement is a domain-totality correction for
`SelectedEntryAtlasProducedBranchData`: payload functions are total over their
guards, so the stopped payload guards must include the displayed Case 2 active
pivot condition.

The Lean target should prove only:

- active-refined guard definitions;
- active-region guard completeness;
- continuing child progress from the active-continuing guard.
- finite source-data records packaging existing continuing,
  actual-width-stopped, and row-exhausted-stopped displayed Case 2 frontier
  payloads.

It must not construct source-production payloads, analytic atlas fields,
normal crossings, pole order, or RLCT.

## Independent Review Result

Xhigh read-only reviewer `Socrates` found two medium issues:

1. The row-exhausted source-suffix record was not total over the semantic
   row-exhausted stopped guard, because the source-suffix payload also needs
   `S + 1 <= L`.
2. The source-data layer is recurrence-valued in the displayed coefficient
   ring `R`, while the all-pivot producer socket is still generic in
   `alpha`.

Resolution:

- Lean now defines
  `case2AllPivotRowExhaustedSourceSuffixGuard`, a suffix-refined row-exhausted
  guard, and the row-exhausted source-suffix constructor is total over that
  refined guard.
- The documents now state that this is an `R`-valued finite source-data layer.
  A final generic `AoyagiRecurrenceBranchState L n alpha` producer must either
  specialize `alpha` to the displayed value type, eventually `ℝ`, or add an
  explicit transport from displayed pivot values into `alpha`.

Re-review result: PASS.  Socrates found one low documentation drift in the
reproduction nonclaims; the controller corrected it to say that this slice
does construct finite source-data packages but not analytic producer payloads
or final `SelectedEntryAtlasProducedBranchData`.

Residual risks:

- The final producer still needs chart tokens, produced points, chart-domain
  and source-domain witnesses, state laws, and center alignment.
- A generic `alpha` recurrence producer still needs specialization to `R`/`ℝ`
  or an explicit value transport.
- Final-stage row-exhausted/no-suffix terminal data remains separate from the
  source-suffix row package.
