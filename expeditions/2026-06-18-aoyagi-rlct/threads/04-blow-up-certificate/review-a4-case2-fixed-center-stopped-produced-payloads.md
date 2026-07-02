# Review - A4 Case 2 fixed-center stopped produced payloads

Date: 2026-07-02.

Reviewer: McClintock, xhigh read-only source/API review.

Verdict: pass after precision fixes.

## Findings Applied

The source-suffix row guard is not disjoint from the terminal-last guard.
`case2AllPivotRowExhaustedSourceSuffixGuard` includes `s.S + 1 <= L`, while
`case2AllPivotRowExhaustedTerminalLastGuard` includes `s.S + 1 = L`.  The docs
were corrected to describe these as separate APIs/packages, not exclusive
subcases.

The source-data structure formerly named as generic row-exhausted stopped data
was renamed to
`Case2AllPivotRowExhaustedSourceSuffixProducedSourceData`, because its guard is
specifically the source-suffix row-exhausted guard.

## Confirmed

The row source-data hardening is source data, not a placeholder.  The
`sourceRows`, `sourceTail`, and definitional equality fields keep the
row-exhausted records in `Type`; they are not `Unit`, `True`, `PUnit`,
`Nonempty`, or `SourceProductionObligation`.

The terminal-last record stores `sourceTail` for bookkeeping, but the
terminal-last frontier proposition does not consume it.  This proves no
semantic property of the tail in the no-suffix terminal-last case.

The public payload constructors take a supplied `chartEquiv` and do not expose
the private canonical finite-subtype chart equivalence or displayed chart
index.  They remain fixed-current-center payload constructors, not
`SelectedEntryAtlasProducedBranchData`.

## Verification Scope

The reviewer requested the usual banking gates: focused module builds, direct
warning checks, full local `lake build DLNFibre`, `lean/scripts/sorries`,
`git diff --check`, and a targeted placeholder-source-data grep.
