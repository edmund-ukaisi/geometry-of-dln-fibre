# Review - A2 retained-passive Case 2 synthetic data

Reviewer: Ampere the 3rd, xhigh

## Verdict

No blockers.

## Checks

The definition `case2PostPivotRetainedPassiveData` is correctly scoped as a
synthetic two-edge retained-passive datum.  Its endpoint family is exactly the
Case 2 post-pivot chain

```text
tau -> Case2ResidualColIndex n S (J+1) -> Case2ResidualRowIndex n S (J+1).
```

The theorem does not claim source production or longer-suffix transport.

The determinant-chart proof is mathematically correct.  The retained-passive
determinant chart asks only for `IsUnit Ctop.det` and determinant units for
the passive `A1` blocks; the synthetic datum sets these matrices to `1`.
There is no unnecessary finiteness/equality hypothesis on `tau`.

The residual-factor theorem preserves the factor order and successor endpoint
orientation.  The two-edge product unfolds as `C 1 * C 0`; in the concrete
Case 2 family, `C 1` is the post-pivot residual block and `C 0` is the
following factor.  The source-shaped readout uses the successor `(S,J+1)`
center and the endpoint equivalence
`eNext : tau ~= Case2ResidualColIndex n S (J+1)`.

The reproduction and statement card match the Lean theorem.  They record the
synthetic fields, the determinant-chart reduction, the `C 1 * C 0` order, and
the retained entrywise successor-source readout hypothesis.

## Follow-up Applied

The statement card now lists the successor-continuation hypothesis
`hnext : J + 2 <= prefixMinNat n (S + 1)` explicitly.  Lean also has a
content-named alias

```text
case2PostPivotRetainedPassiveData_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_entrywise
```

in addition to the downstream-socket name
`case2PostPivotRetainedPassiveData_hdataFactor_of_entrywise`.
