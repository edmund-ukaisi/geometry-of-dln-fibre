# Review - selected-entry multi-chart certificate

Date: 2026-06-23.

Reviewer: xhigh reviewer `McClintock`.

Verdict: PASS.

## Scope

Reviewed the current A4 selected-entry multi-chart certificate slice:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`
- `reproduction-selected-entry-multi-chart-certificate-a4.md`
- `statement-card-a4-selected-entry-multi-chart-certificate.md`
- the corresponding `thread.md` summary.

## Findings

No blocking fidelity, mathematical, or overclaiming issues were found.

The Lean wrapper
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate` is finite
chart-family bookkeeping.  Its charts are indexed by a supplied equivalence
`Fin center.card ≃ center`, and each chart delegates to the existing one-pivot
selected-entry certificate for the pivot selected by that equivalence.

The finite exponent summaries stay inside `exponentData`: each chart has loss
exponent `1`, formal Jacobian/prior exponent `card(center.erase pivot)`, ratio
`center.card / 2`, chart count `1` at that ratio, finite minimum
`center.card / 2`, and finite exponent order `1`.

The documentation keeps the intended boundary: no analytic atlas coverage,
transition regularity, analytic Jacobian/volume-form theorem, source
production of successor matrices or post-data, active-ratio lower bound for a
global A0 certificate, pole-order theorem, or RLCT extraction is claimed.

## Verification

The reviewer reported:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
git diff --check
```

passed.  The controller also reran the focused Lean build before recording this
review.
