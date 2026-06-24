# Review - A4 Case 2 source-selected finite chart production

Date: 2026-06-24.

Reviewer: xhigh independent reviewer `Meitner`.

Verdict: pass.

## Scope Reviewed

- Lean changes in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`;
- reproduction note
  `reproduction-case2-source-selected-finite-chart-production-a4.md`;
- statement card
  `statement-card-a4-case2-source-selected-finite-chart-production.md`.

## Findings

No mathematical or Lean-fidelity blocking findings.

The generic theorem reuses existing finite chart coverage, destructures the
selected-entry chart point, extends erased residual coordinates to ambient
residual coordinates, and proves the `sourceChartPoint` adapter equality
before reusing the chart-map equality.

The Case 2 theorem specializes this finite production to the residual-block
center and then uses the existing source-selected chart-map bridge.  The result
is finite selected-entry source-coordinate production only.

No quiver-paper dependency was found.  The comments and docs explicitly
exclude analytic atlas coverage, transition regularity, successor/suffix
production, full DLN normal crossings, pole order, and RLCT extraction.

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
