# Review - Case 2 source-chart selected-entry microcertificate adapter

Date: 2026-06-23.

Reviewer: Erdos, xhigh effort, read-only.

## Scope

Reviewed the uncommitted A4/A0 local adapter slice:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`
- `reproduction-case2-source-chart-selected-entry-microcertificate-adapter-a4.md`
- `statement-card-a4-case2-source-chart-selected-entry-microcertificate-adapter.md`
- expedition ledger/thread updates

The review checked source/math overclaiming, Lean API mismatch, dependency
boundary issues, and documentation mismatch.

## Findings

No blocking source/math overclaiming or Lean API issue was found.  The Lean
statements stay inside the intended local boundary: they present the displayed
continuing Case 2 source chart point inside the existing one-chart
selected-entry finite microcertificate.  They do not claim chart coverage,
total DLN loss, an analytic Jacobian theorem, pole order, or RLCT.

Two documentation findings were addressed after review:

- `priorities.md` needed a blank line before the next numbered item.
- the reproduction display for the formal determinant needed to show the
  erased-subtype residual function `fun e => residual e.1`.

## Verification

The reviewer ran:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
scripts/sorries DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean
git diff --check
```

The focused build passed.  The targeted hygiene check reported:

```text
0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

`git diff --check` passed.

## Boundary

The review used Aoyagi-local Lean and expedition artifacts only.  It did not
use the quiver-based paper.  Direct PDF text extraction was unavailable in the
reviewer environment, so page-level source references remain the source
boundary for this slice.
