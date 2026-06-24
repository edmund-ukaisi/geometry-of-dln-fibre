# Review - A4 Case 2 chart-index source-selected boundary/QP bridge

Date: 2026-06-24.

Reviewer: xhigh independent reviewer `Nash`.

Verdict: pass.

## Scope Reviewed

- Lean changes in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`;
- reproduction note
  `reproduction-case2-chart-index-source-selected-boundary-qp-a4.md`;
- statement card
  `statement-card-a4-case2-chart-index-source-selected-boundary-qp.md`;
- underlying supplied-boundary API in
  `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

## Findings

No mathematical or Lean-fidelity blocking findings.

The chart index is tied to `case2ResidualBlockPivotEntries` through
`finsetSubtypeChartEquiv` in the all-pivot certificate, and the wrapper passes
exactly the selected subtype membership `.2` into
`Case2SourceSelectedSuppliedChartFamilyBoundary.of_case2Succ_updateSelected`.

The `Q/P` wrapper is exactly the existing
`Case2SourceSelectedSuppliedChartFamilyBoundary.sourceSelectedQP_sourceChartMap`
projection instantiated on that boundary.  The local bindings `row`, `col`,
`A`, `Csrc`, and `Ctr` match the source-selected theorem.

No overclaiming was found in the Lean comments or docs.  The slice explicitly
does not prove chart coverage, analytic atlas or regularity, chart-produced
post-data, global normal crossings, pole order, or RLCT extraction.

The only finding was stale documentation status: the reproduction note still
said "before Lean formalisation" and the statement card still said
"Pending."  The controller updated both after the green gates.

## Verification

The reviewer ran:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
```

The controller additionally ran:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

The sorry audit reported `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.
