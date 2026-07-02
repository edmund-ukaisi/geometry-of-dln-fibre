# Review - A4 all-pivot producer recurrence termination

Date: 2026-07-02.

Status: PASS.

## Scope For Review

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotProducerTermination.lean`
- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotProducerShell.lean`
- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryBranchProgressBridge.lean`
- `threads/04-blow-up-certificate/reproduction-a4-all-pivot-producer-recurrence-termination.md`
- `threads/04-blow-up-certificate/statement-card-a4-all-pivot-producer-recurrence-termination.md`

## Source/Scope Review

Reviewer: `Plato`.

Verdict: PASS.  The review was read-only and found no blocking findings.

The reviewer confirmed that the adapter uses the same all-pivot certificate
expected by the shell.  The shell's termination argument is over

```text
selectedEntryCenterSqFormalJacobianChartFamilyCertificate
  (K := Real) hcenter chartEquiv
```

and the adapter passes exactly this certificate to
`selectedEntryRecurrenceBranchTerminationData`.

The reviewer also confirmed that `sourceProduction` remains an explicit
adapter parameter and is passed through unchanged to the shell.  The docs say
that source production remains supplied, and their nonclaim sections exclude
source-production payloads, normal crossings, pole order, and RLCT extraction.

## API Note

The adapter imports `SelectedEntryBranchProgressBridge` only for
`selectedEntryRecurrenceBranchTerminationData`.  This is acceptable for the
current slice.  If dependency layering becomes important later, the
termination-data adapters could be split into a smaller module.

## Controller Verification

The controller ran:

```text
env LEAN_NUM_THREADS=3 lake build \
  DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotProducerTermination
env LEAN_NUM_THREADS=3 lake build DLNFibre
lean/scripts/sorries
git diff --check
```

The focused build, full local build, no-sorry audit, and whitespace check
passed.  The no-sorry audit reported:

```text
0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

The full local build completed with pre-existing unrelated warnings in other
modules.

## Nonclaim Boundary

This adapter constructs no source-production data, branch guard coverage,
continuing children, stopped-branch terminal payloads, successor or suffix
production, normal crossings, pole order, or RLCT.  It only fills the
all-pivot producer's branch-termination field in the recurrence-aware
branch-state case from existing recurrence termination data.
