# Review - Case 1 source-chart selected-entry microcertificate adapter

Date: 2026-06-23.

Reviewer: Carson, xhigh effort, read-only.

## Scope

Reviewed the uncommitted A4/A0 Case 1 local adapter slice:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`
- `reproduction-case1-source-chart-selected-entry-microcertificate-adapter-a4.md`
- `statement-card-a4-case1-source-chart-selected-entry-microcertificate-adapter.md`
- expedition ledger/thread updates

The review checked formalisation/API correctness, source/math overclaiming,
and in particular whether the selected-old `Unit` pivot was incorrectly
identified with a hidden old source label.

## Findings

No blocking or non-blocking findings were reported.

The selected-old specialization keeps the pivot as the finite
`Sum.inl ()` token and does not identify it with the hidden old source label.
The reproduction and statement card preserve the same boundary.

## Verification

The reviewer ran:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
```

The focused build passed:

```text
Build completed successfully (3292 jobs).
```

The reviewer also checked the focused Lean file for `sorry`, `axiom`,
`native_decide`, and `#exit`; no matches were found.

## Boundary

The review used local Lean/Aoyagi expedition artifacts and boundary docs.
Direct PDF text extraction was unavailable in the reviewer environment, so
the review did not quote raw extracted PDF text.  No quiver-paper evidence was
used.
