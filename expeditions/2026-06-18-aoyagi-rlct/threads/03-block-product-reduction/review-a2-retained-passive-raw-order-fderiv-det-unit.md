# Review - A2 Retained-Passive Raw-Order FDeriv Determinant Unit

Date: 2026-06-26.

Status: reviewed; no blockers found.

Reviewer: xhigh read-only explorer `Hilbert the 4th`.

## Verdict

Pass.

## Findings

No critical, high, medium, or low findings.

## Checked Points

- The Lean statements have the intended ambient `fderiv` scope on
  `TopologyTuple`, with the sole source hypothesis
  `z in topologyTupleDetChartSet`.
- The proof uses openness of the source and target chart sets exactly to turn
  the chart inverse identities into eventual equalities in ambient
  neighborhood filters before applying the ordinary chain rule.
- The determinant-unit theorem takes determinants in
  `Dg_y.comp Df_z = id`, obtains `det(Dg_y) * det(Df_z) = 1`, and concludes
  unitness of `det(Df_z)` over `R = real`.
- The reproduction note and statement card do not claim an explicit derivative
  formula, determinant formula, density, measure pushforward, source-rank
  coverage, normal-crossing theorem, pole order, or RLCT.
- No quiver source or quiver result is used by the reviewed slice.

## Reviewer Verification

The reviewer reported that

```text
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
git diff --check
```

passed on the reviewed dirty files.  The controller separately reran the
project build checks before commit.
