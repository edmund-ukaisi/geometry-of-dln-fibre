# Statement card - A0 chart-certificate Jacobian-prior loss shift

## Lean Names

File:

- `lean/DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean`

Names:

- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingChartCertificate.jacobianPriorLossShift`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingChartCertificate.jacobianPriorLossShift_lossExp`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingChartCertificate.jacobianPriorLossShift_jacobianPriorExp`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingChartCertificate.exponentData_jacobianPriorLossShift`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingChartCertificate.exponentData_exponentMinimum_jacobianPriorLossShift`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingChartCertificate.exponentData_exponentOrder_jacobianPriorLossShift`

## Claim

Multiplying a supplied chart certificate's Jacobian/prior monomial by
`prod_j coord_j^(m * k_j)` produces another chart-certificate spine whose
projected finite exponent data is the existing finite
`jacobianPriorLossShift m`.

## Proved

The shifted certificate leaves loss exponents unchanged and changes
Jacobian/prior exponents by

```text
h_j ↦ h_j + m*k_j.
```

It projects to the exponent-data shift:

```text
(C.jacobianPriorLossShift m).exponentData
  = C.exponentData.jacobianPriorLossShift m.
```

The projected finite minimum and order satisfy:

```text
(C.jacobianPriorLossShift m).exponentData.exponentMinimum
  = C.exponentData.exponentMinimum + m/2

(C.jacobianPriorLossShift m).exponentData.exponentOrder
  = C.exponentData.exponentOrder.
```

## Assumed

A supplied `AoyagiNormalCrossingChartCertificate C` and a natural shift
parameter `m`.

## Deferred

Regular-coordinate construction, chart coverage, analytic Jacobian/volume-form
control, regular-suspension normal-crossing certificate construction, pole
order, RLCT additivity, and the extraction theorem.

## Verification

Lean and repository gates passed through the shared-store build wrapper:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.NormalCrossingInterface
cd lean && scripts/lb
cd lean && scripts/sorries
git diff --check
```

The focused module build completed successfully with 1174 jobs.  The full
library build completed successfully with 3898 jobs.  The sorry audit reported
`0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
