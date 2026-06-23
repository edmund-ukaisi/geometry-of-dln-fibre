# Statement card - A0 normal-crossing Jacobian-prior loss shift

## Lean Names

File:

- `lean/DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean`

Names:

- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingExponentData.jacobianPriorLossShift`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingExponentData.jacobianPriorLossShift_lossExp`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingExponentData.jacobianPriorLossShift_jacobianPriorExp`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingExponentData.activePairs_jacobianPriorLossShift`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingExponentData.mem_activePairs_jacobianPriorLossShift`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingExponentData.ratioAt_jacobianPriorLossShift_of_mem_activePairs`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingExponentData.exponentMinimum_jacobianPriorLossShift`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingExponentData.coordsInChartAtRatio_jacobianPriorLossShift`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingExponentData.countInChartAtRatio_jacobianPriorLossShift`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingExponentData.minCoordsInChart_jacobianPriorLossShift`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingExponentData.minCountInChart_jacobianPriorLossShift`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingExponentData.exponentOrder_jacobianPriorLossShift`

## Claim

For finite normal-crossing exponent data, replacing every Jacobian/prior
exponent `h_j` by `h_j + m*k_j` shifts all active ratios and the finite
minimum by `m/2`, and preserves the minimum-coordinate chart counts and finite
order.

## Proved

For every active pair `p`:

```text
(D.jacobianPriorLossShift m).ratioAt p = D.ratioAt p + m/2.
```

Consequently:

```text
(D.jacobianPriorLossShift m).exponentMinimum
  = D.exponentMinimum + m/2

(D.jacobianPriorLossShift m).minCoordsInChart c
  = D.minCoordsInChart c

(D.jacobianPriorLossShift m).minCountInChart c
  = D.minCountInChart c

(D.jacobianPriorLossShift m).exponentOrder
  = D.exponentOrder.
```

The ratio-specific coordinate and count variants are also proved:

```text
(D.jacobianPriorLossShift m).coordsInChartAtRatio (q + m/2) c
  = D.coordsInChartAtRatio q c

(D.jacobianPriorLossShift m).countInChartAtRatio (q + m/2) c
  = D.countInChartAtRatio q c.
```

## Assumed

Only the supplied finite exponent data `D` and natural shift parameter `m`.
The ratio theorem assumes the coordinate is active.

## Deferred

Analytic construction of regular coordinates, chart coverage, Jacobian/volume
form computation, normal-crossing certificate construction, RLCT additivity,
and the post-Theorem-3 regular-suspension certificate.

## Verification

Focused Lean check passed:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean
```

Full verification is recorded after the module/full build closeout.
