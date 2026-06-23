# Review - selected-entry multi-chart source-point adapter

Date: 2026-06-23.

Reviewer: xhigh reviewer `Einstein`.

Verdict: PASS.

## Scope

Reviewed the current A4/A0 selected-entry multi-chart source-point adapter
slice:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`
- `reproduction-selected-entry-multi-chart-source-point-adapter-a4.md`
- `statement-card-a4-selected-entry-multi-chart-source-point-adapter.md`

## Findings

No blocking fidelity, mathematical, or overclaiming issues were found.

The Lean slice is faithful to the reproduction note.  The new `sourceChartPoint`
definition delegates chart `c` to the one-pivot source point at `chartEquiv c`,
and the chart-map, loss, unit, and formal determinant lemmas are all chartwise
delegations, not new analytic claims.

The monomial identities remain finite source-point presentations: they rewrite
through the finite certificate's `loss_monomial` and
`jacobianPrior_monomial`.  They do not assert atlas coverage, transition
regularity, analytic Jacobian/volume-form control, A0/global normal-crossing
data, pole order, or RLCT extraction.

Recommendation: keep this generic presentation layer.  It is thin and useful
for later all-pivot Case 1/2 wrappers without duplicating the same source-point
lemmas per concrete center.

## Verification

The reviewer reported:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
git diff --check -- lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean
```

passed.  The controller also ran the focused Lean build before review.
