# Review - A2 selected-entry all-pivot producer shell

Date: 2026-06-29.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotProducerShell.lean`;
- `lean/DLNFibre.lean`;
- `reproduction-a2-selected-entry-all-pivot-producer-shell.md`;
- `statement-card-a2-selected-entry-all-pivot-producer-shell.md`.

## Verdict

PASS.

## Reviewers

- Xhigh source/scope reviewer `Darwin the 4th`: PASS.  The docs correctly say
  Aoyagi pp. 15-22 support the selected-entry coordinate calculation only, and
  the shell is expedition interface bookkeeping rather than a source-production
  theorem.
- Xhigh Lean/API reviewer `James the 4th`: PASS.  The declaration assembles
  all analytic fields over `selectedEntryAllPivotAnalyticAtlasContext hcenter
  chartEquiv`, keeps `sourceProduction` and `termination` explicit over the
  same `BranchState`, and does not create a false-guard or default branch
  producer internally.

## Verification

The controller ran local checks:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotProducerShell
env LEAN_NUM_THREADS=3 lake env lean -E warning DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotProducerShell.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
lean/scripts/sorries
git diff --check
env LEAN_NUM_THREADS=3 lake env lean -E warning /tmp/aoyagi_producer_shell_axioms.lean
```

The focused module build, direct warning-level file check, full `DLNFibre`
build, sorry scan, and whitespace check passed.  The direct axiom probe for
`SelectedEntrySignedBox.CenterCoord.selectedEntryAllPivotSuppliedAnalyticAtlasProducer`
reports only `[propext, Classical.choice, Quot.sound]`.

## Nonclaims Checked

The shell does not construct source production, prove branch termination, prove
branch guard exhaustiveness, prove transition semantics for branch states,
extract normal crossings, compute pole order, or extract an RLCT.
