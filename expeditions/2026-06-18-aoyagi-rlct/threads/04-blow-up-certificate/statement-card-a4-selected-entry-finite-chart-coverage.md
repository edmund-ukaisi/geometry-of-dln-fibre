# Statement card - A4 selected-entry finite chart coverage

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Names:

- `selectedEntryCenterSqFormalJacobianChartCertificate.exists_oneChartPoint_chartMap_eq_value_of_pivot_ne_zero`
- `selectedEntryCenterSqFormalJacobianChartCertificate.exists_oneChartPoint_chartMap_eq_value_of_forall_eq_zero`
- `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exists_chartPoint_chartMap_eq_value_of_chart_pivot_ne_zero`
- `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exists_chartPoint_chartMap_eq_value`

## Claim

For a finite selected-entry center, the one-pivot chart map has an explicit
preimage for any finite value whose selected pivot coordinate is nonzero.  The
zero value has a preimage in every one-pivot chart.  Consequently, if the
finite center is nonempty, the all-pivot selected-entry chart-family map
covers every finite center value.

## Inputs Kept Explicit

- a finite center `center : Finset iota`;
- a selected pivot `pivot : center` for the one-pivot inverse;
- an ordered field coefficient type;
- for the one-pivot nonzero inverse, the hypothesis `value pivot != 0`;
- for the zero inverse, the hypothesis `forall i, value i = 0`;
- for the all-pivot family, a nonempty finite center and a supplied
  equivalence `Fin center.card ~= center`.

## Proved

The nonzero one-pivot inverse chooses

```text
u = value pivot
residual i = value i / value pivot
```

on center coordinates.  The selected-entry chart map then sends the pivot to
`value pivot` and every other center coordinate to
`value pivot * (value i / value pivot) = value i`.

The zero one-pivot inverse chooses `u = 0` and all residuals zero.  The
all-pivot theorem splits a finite value into the zero case and the case of a
nonzero coordinate, then chooses the chart whose pivot is that coordinate.

## Not Proved

This is finite selected-entry map coverage only.  It does not prove analytic
chart domains or neighbourhood coverage, transition regularity, arbitrary
non-displayed Aoyagi source-coordinate formulas, source production of
successor matrices or suffix products, analytic Jacobian or volume-form
control, a full `AoyagiNormalCrossingChartCertificate`, pole order, or RLCT
extraction.

## Verification

Controller ran:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

The focused build, full-library build, no-sorry/no-axiom scan, and diff
hygiene check passed through the shared-store `lb` workflow.  The full build
emitted only unrelated pre-existing Core warnings.

## Review

Xhigh review passed with no blocking findings.  See
`review-selected-entry-finite-chart-coverage-a4.md`.
