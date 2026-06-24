# Review - A4 Case 2 all-pivot source-selected monomial/principalization adapter

Date: 2026-06-24.

Reviewer: xhigh independent reviewer `Godel`.

Verdict: no blocking findings.

## Scope Reviewed

- Lean changes in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`;
- reproduction note
  `reproduction-case2-all-pivot-source-selected-monomial-principalization-a4.md`;
- statement card
  `statement-card-a4-case2-all-pivot-source-selected-monomial-principalization.md`.

## Findings

No blocking findings.

The slice stays within finite selected-entry algebra.  The reproduction and
statement card explicitly separate Aoyagi's displayed top-left pivot from the
Lean all-pivot finite scaffold, and they do not claim source-displayed
formulas for every non-top-left pivot.

The Lean additions match the reproduction: the new adapters pick the chart
pivot through `finsetSubtypeChartEquiv`, rewrite to
`case2SourceSelectedChartMapOfMem`, and transport existing generic
selected-entry facts by `simpa` rather than proving new analytic content.

No hidden analytic Jacobian/volume, coverage, regularity, pole-order, or RLCT
claim was found.  The only residual naming risk is that exported names such as
`centerIdeal...` and `jacobianPrior...` are concise, so downstream use must
preserve the docstring caveats that these are finite/formal statements.

## Verification Noted

The reviewer independently checked:

```text
git diff --check
cd lean && lake env lean DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean
```

The controller gate additionally used the expedition wrapper:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

The sorry audit reported `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.
