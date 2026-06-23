# Review - A4 selected-entry finite chart coverage

Date: 2026-06-23.

Reviewer: xhigh read-only reviewer `Arendt`.

Status: passed.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`;
- `reproduction-selected-entry-finite-chart-coverage-a4.md`;
- `statement-card-a4-selected-entry-finite-chart-coverage.md`.

The review checked whether the finite inverse lemmas match the elementary
selected-entry formula, whether the all-pivot theorem has the right nonempty
finite-center shape, and whether the slice overclaims analytic atlas, source,
transition, normal-crossing, pole-order, or RLCT consequences.

## Findings

No blocking findings.

The Lean inverse matches the elementary formula.  In the nonzero pivot case,
the proof sets `u = value pivot` and residuals `value i / value pivot`, then
proves that the chart map equals `value`.  In the zero case, it uses `u = 0`
and zero residuals.

The all-pivot theorem has the right nonempty-center hypothesis and proves only
finite chart-map surjectivity onto `center -> K`.  It splits into the zero
case and the case of a nonzero coordinate, then chooses the corresponding
pivot chart.

The reviewer did not see analytic atlas, source-production, transition, or
RLCT overclaiming.  The Lean docstrings and reproduction boundary explicitly
limit the claims to finite selected-entry map coverage.

## Verification

The reviewer ran:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
```

The focused build passed.

## Verdict

Acceptable to checkpoint.
