# Reproduction - A2 retained-passive inverse-Jacobian chart-side measurability wrapper

## Shape

The raw-order retained-passive inverse-Jacobian residual and finite-integral
handoffs both use the identity retained-passive source family

```text
EFam = forall p : Fin (M + 1),
  reverseVertex W p.castSucc ->L[R] reverseVertex W p.succ
Cedge = fun E : EFam => E.
```

Their previous front ends still asked for source-space residual positive-set
measurability:

```text
MeasurableSet {x : EFam | 0 < residualSquareSum x}.
```

This input is not an analytic residual/integrability theorem.  It is the same
finite fixed-base coordinate measurability already proved for the canonical
identity source:

```text
measurableSet_residualSquareSum_pos_retainedPassiveP13Canonical_id.
```

## Calculation

The wrapper proof is deliberately small.  It defines the same `EFam` as the
raw-order inverse-Jacobian handoff and sets

```text
hpos_meas :=
  measurableSet_residualSquareSum_pos_retainedPassiveP13Canonical_id
```

after the usual definitional simplification of `EFam`.  It then delegates to

```text
residualSourceHypotheses_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian.
```

The determinant-chart hypotheses remain exactly where they were:

```text
for m.restrict S-a.e. z, residualSquareSum (directChart z) > 0,
integral over m.restrict S of residualSquareSum (directChart z)^(-t) is finite.
```

The finite-integral wrapper also keeps the local loss lower bound and local
density nonnegativity/upper-bound hypotheses.

## Lean result

New Lean names:

```text
residualSourceHypotheses_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_chartSide
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_chartSide
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalJacobianMeasure.lean
```

## Boundary

This removes only the source-space residual positive-set measurability field
from the raw-order inverse-Jacobian residual and finite-integral handoffs.  It
does not prove determinant-chart a.e. residual positivity, finite residual
negative-power integrability, local loss lower bounds, density bounds,
selected-entry residual integrability, source-rank coverage, original external
source-prior transport, normal crossings, pole order, or RLCT.
