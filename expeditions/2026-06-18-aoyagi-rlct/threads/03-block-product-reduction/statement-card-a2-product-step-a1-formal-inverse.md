# Statement Card - A2 product-step A1 formal inverse

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`

## Claim

Lean proves the record-level p. 13 one-step coordinate maps are formal
inverses on the `A1` determinant-unit locus.  The raw and chart
determinant-chart inverse theorems remain available as wrappers.

## Lean Names

```text
productReductionStepCoordinate_left_inverse_of_isUnit_A1
productReductionStepCoordinate_right_inverse_of_isUnit_A1
productReductionStepCoordinate_left_inverse
productReductionStepCoordinate_right_inverse
```

## Inputs

- finite matrix index types for the retained top block and residual-source
  block;
- `IsUnit x.A1.det` for the raw-to-chart-to-raw inverse;
- `IsUnit y.A1.det` for the chart-to-raw-to-chart inverse;
- the older wrapper theorems additionally require the relevant determinant
  chart hypotheses.

## Not Proved

This does not weaken the determinant-chart domain for analytic chart,
derivative, or measure results.  It does not prove a local inverse for the
original DLN parameter space, source-rank coverage, source-measure transport,
density/Jacobian identity, normal crossings, pole order, or RLCT extraction.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.ProductReduction
```

Passed on 2026-06-26.
