# Review - selected-entry local ratio chart count

Date: 2026-06-23.

Reviewers: xhigh source/fidelity scout `Kant`; xhigh Lean/API scout
`Copernicus`; controller check.

Status: passed for the finite-local claim.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`;
- `reproduction-selected-entry-ratio-chart-count-a4.md`;
- `statement-card-a4-selected-entry-ratio-chart-count.md`.

The review checked whether the new count lemmas are just finite bookkeeping on
the one-chart selected-entry microcertificates, whether the displayed ratios
use the full center cardinality rather than the erased-center count, and
whether the docs avoid global A0 and pole-order overclaims.

## Findings

No mathematical or source-fidelity issue remains for the finite-local claim.

The source-fidelity scout confirmed that Aoyagi does not state a Lean-style
`countInChartAtRatio = 1` lemma, but the statement is a definitional
consequence of the already reproduced local chart: there is one chart, one
active normal-crossing coordinate, and the existing local ratio computation
identifies that coordinate's ratio.

The Lean/API scout confirmed the useful theorem surface:

```text
selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_countInChartAtRatio_centerCard_div_two_eq_one
case2DisplayedCenterSqFormalJacobianChartCertificate.exponentData_countInChartAtRatio_centerCard_div_two_eq_one
case1SelectedOldCenterSqFormalJacobianChartCertificate.exponentData_countInChartAtRatio_nonpivotCount_add_one_div_two_eq_one
case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.exponentData_countInChartAtRatio_nonpivotCount_add_one_div_two_eq_one
```

The optional `minCountInChart = 1` wrappers are also sound because the local
finite minimum was already proved to equal the same local ratio.

The ratio orientation is correct:

- generic selected-entry: `center.card / 2`;
- Case 2: `card(case2ResidualBlockPivotEntries n S J) / 2`;
- Case 1: `(1 + J1 * (n(S+1)-J)) / 2`.

## Nonclaims Checked

The slice does not prove a global A0 chart-family count, an all-chart upper
bound for the DLN resolution, Aoyagi's pole order, Theorem 2's order formula,
chart coverage, transition regularity, source production, successor recurrence
data, an analytic Jacobian/volume-form theorem, or RLCT extraction.

For the Case 1 selected-old specialization, the `Unit` old-generator token
remains finite bookkeeping and not a source construction of the hidden old
label.

## Verification

Controller ran:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
cd lean && scripts/lb
cd lean && scripts/sorries
git diff --check
```

The focused module build, full library build, no-sorry audit, and diff hygiene
check passed through the shared-store workflow.  The full build emitted only
pre-existing Core/style warnings unrelated to this slice.
