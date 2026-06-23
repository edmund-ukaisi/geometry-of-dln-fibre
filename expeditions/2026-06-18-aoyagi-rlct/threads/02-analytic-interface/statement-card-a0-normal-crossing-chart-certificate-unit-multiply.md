# Statement card - A0 chart-certificate unit multiplication

## Lean Names

File:

- `lean/DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean`

Names:

- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingChartCertificate.unitMultiply`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingChartCertificate.unitMultiply_lossExp`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingChartCertificate.unitMultiply_jacobianPriorExp`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingChartCertificate.exponentData_unitMultiply`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingChartCertificate.exponentData_exponentMinimum_unitMultiply`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingChartCertificate.exponentData_exponentOrder_unitMultiply`

## Claim

Multiplying the loss and Jacobian/prior displays of a supplied
`AoyagiNormalCrossingChartCertificate` by supplied chartwise unit factors
produces another chart-certificate spine with the same chart maps,
coordinates, loss exponents, Jacobian/prior exponents, and projected finite
exponent data.

## Proved

Given supplied identities

```text
loss' (C.chartMap c u)
  = lossFactor c u * C.loss (C.chartMap c u)

jacobianPrior' c u
  = jacobianPriorFactor c u * C.jacobianPrior c u
```

and supplied unit witnesses for both factors, Lean constructs the new
certificate with unit fields

```text
lossFactor c u * C.lossUnit c u
jacobianPriorFactor c u * C.jacobianPriorUnit c u.
```

The exponent projection is definitionally unchanged:

```text
(C.unitMultiply ...).exponentData = C.exponentData.
```

Therefore the projected finite exponent minimum and order are unchanged.

## Assumed

A supplied chart certificate, two replacement functions, pointwise
multiplicative identities relating them to the old functions on chart images,
and pointwise unit witnesses for the two factors.

## Deferred

Construction of analytic unit neighborhoods, chart coverage, a Jacobian or
volume-form theorem, global normal-crossing certificate production, pole
order, RLCT extraction, and any regular-coordinate additivity theorem.

## Verification

Lean and repository gates passed through the shared-store wrapper:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.NormalCrossingInterface
cd lean && scripts/lb
cd lean && scripts/sorries
git diff --check
```

The focused build completed successfully with 1174 jobs.  The full build
completed successfully with 3901 jobs, with only pre-existing Core/style
warnings.  The sorry audit reported
`0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
