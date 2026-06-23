# Review - A4 Case 1 selected-entry chart-family data

Date: 2026-06-23.

Reviewer: xhigh final reviewer `Peirce`.

Status: passed after artifact-link fix.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`;
- `reproduction-case1-selected-entry-chart-family-data-a4.md`;
- `statement-card-a4-case1-selected-entry-chart-family-data.md`;
- the A4 entries in `priorities.md`, `claims.md`, `theorem-ledger.md`, and
  `threads/04-blow-up-certificate/thread.md`.

The review checked Lean statement correctness, source fidelity, API scope,
overclaiming boundaries, and artifact links.

## Findings

No Lean or mathematical blockers were found.

The Lean additions are conservative.  `Case1CenterSelectedEntryChartFamilyData`
is the Case 1 specialization of `SelectedEntryChartFamilyData`, with named
subtype pivots for the selected-old token and the displayed top-left row-strip
entry.  The `.value`, selected-variable, `centerSq`, and `centerIdeal`
wrappers are source-facing names over existing generic finite facts.  The
`@[simp]` projection and value lemmas are narrow reflexive reductions; no
broad overlapping-simp risk was found.

The scope is appropriately limited.  The Lean docstrings and expedition notes
do not claim chart coverage, chart or transition regularity, analytic Jacobian
control, global A0 data, pole order, or RLCT extraction.  The source role is
consistent with the existing Case 1 source notes: the center is the old
exceptional token plus the row strip, and only the selected-old and top-left
row-strip charts are treated as source-displayed.

## Incorporated Fix

The reviewer found that the ledgers and statement card referred to this review
artifact before it existed.  This review note was added, and the reproduction
status was changed from pending to reviewed.

## Residual Risk

The reviewer could not independently extract Aoyagi PDF pp. 16-17 in the VM
because PDF text extraction tools are unavailable.  This review therefore
relies on the existing source-audited Case 1 notes already in the expedition.

## Verification

Controller ran:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic
cd lean && scripts/lb
cd lean && scripts/sorries
git diff --check
```

The focused module build, full-library build, no-sorry audit, and diff hygiene
check passed through the shared-store `scripts/lb` workflow.  The full build
emitted only unrelated pre-existing Core warnings.
