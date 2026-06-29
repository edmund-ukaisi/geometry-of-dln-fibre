# A2 retained-passive chart-produced punctured-sector residual-source socket

## Scope

This note reproduces the measure handoff following the already-reviewed
punctured-sector readout theorem

```text
exists_open_measure_map_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_eq_snd.
```

The source input remains Aoyagi's p. 13 retained-passive product-difference
coordinates, supported by the reproduction for the preceding readout theorem.
There is no new Aoyagi coordinate calculation here.  The new step is only the
measure-theory consequence: if the residual-coordinate marginal on the
punctured sector has residual positivity and finite negative-power integral,
then the chart-produced source measure satisfies the retained-passive
residual-source hypotheses.

## Objects

Fix the Case 2 passive selected-entry data used by the punctured-sector theorem.
Let

```text
center = case2ResidualBlockPivotEntries n S (J + 1),
pivotNext = (J + 2, J + 2) in center,
X = eta x (center -> R).
```

The already-proved theorem gives an open set `V subset X`, with `z0 in V`, and
the chart-produced source measure

```text
mu = Measure.map sourceChart (sourceMeasure.restrict V)
```

is supported on the retained-passive p.13 local source.  It also gives the
exact residual readout map

```text
inverseReadout : EdgeFamily -> center -> R
```

with

```text
Measure.map inverseReadout mu
  = Measure.map Prod.snd (sourceMeasure.restrict V).
```

Write

```text
marginal = Measure.map Prod.snd (sourceMeasure.restrict V).
```

The target socket assumes, for a real exponent `t`,

```text
(A) marginal-a.e. y, 0 < SelectedEntrySignedBox.CenterCoord.residual pivotNext y,
(B) integral over marginal of residual(y)^(-t) is finite.
```

It must prove

```text
mu.restrict localSource = mu,
mu.restrict localSource-a.e. E, 0 < residualSquare(E),
residualNegPowerIntegrableOn localSource mu t.
```

Here `residualSquare(E)` is the fixed-base p.13 residual coordinate square-sum

```text
aoyagiCoordinateSquareSum
  (paperEndpointFixedBaseResidualBlockCoordinateMap ... E).
```

## Pointwise residual comparison

For an edge family `E`, let

```text
value_E : center -> R
value_E c =
  paperEndpointFixedBaseResidualBlockCoordinateMap ... E (residualCoordEquiv.symm c).
```

By definition,

```text
inverseReadout E =
  SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero pivotNext value_E.
```

The fixed-pivot inverse is not a global inverse when the pivot coordinate of
`value_E` is zero.  The positivity hypothesis supplies the missing condition.
Indeed, if

```text
0 < residual pivotNext (inverseReadout E),
```

then `value_E pivotNext != 0`.  Otherwise the pivot coordinate of
`inverseReadout E` is zero, so the selected-entry chart

```text
chartMap pivotNext (inverseReadout E)
```

collapses to the zero vector, and the residual is zero, contradiction.

With `value_E pivotNext != 0`, the fixed-pivot inverse theorem gives

```text
chartMap pivotNext (inverseReadout E) = value_E.
```

Therefore

```text
SelectedEntrySignedBox.CenterCoord.residual pivotNext (inverseReadout E)
  = aoyagiCoordinateSquareSum value_E.
```

Finally, finite reindexing by `residualCoordEquiv.symm` gives

```text
aoyagiCoordinateSquareSum value_E
  = aoyagiCoordinateSquareSum
      (paperEndpointFixedBaseResidualBlockCoordinateMap ... E).
```

Thus on the a.e. set where the inverse-readout residual is positive, the
source residual square-sum is equal to that selected-entry residual.

## Measure transfer

The punctured-sector theorem gives

```text
Measure.map inverseReadout mu = marginal.
```

From assumption (A), `ae_of_ae_map` gives

```text
mu-a.e. E, 0 < residual pivotNext (inverseReadout E).
```

The pointwise comparison above converts this into

```text
mu-a.e. E, 0 < residualSquare(E).
```

The support equality `mu.restrict localSource = mu` converts it to the local
source restricted measure.

For the integral, set

```text
g(y) = ENNReal.ofReal ((residual pivotNext y)^(-t)).
```

The selected-entry residual is measurable because it is the square-sum of the
measurable selected-entry chart coordinates.  Hence `lintegral_map` and the map
identity give

```text
integral_mu g(inverseReadout E) = integral_marginal g(y) < infinity.
```

The same a.e. pointwise comparison gives

```text
ENNReal.ofReal ((residualSquare(E))^(-t))
  = ENNReal.ofReal ((residual pivotNext (inverseReadout E))^(-t))
```

for `mu`-almost every `E`.  By `lintegral_congr_ae`, the source residual
negative-power integral over `mu` is finite.  The support equality again
rewrites this as `residualNegPowerIntegrableOn localSource mu t`.

## Kill conditions

- Kill if the theorem tries to prove assumptions (A) and (B) for an arbitrary
  `sourceMeasure`; they must remain explicit marginal assumptions unless a
  concrete signed-box or product measure is supplied.
- Kill if the result is named or described as determinant-chart Haar transport,
  raw/source Haar transport, original source-prior transport, a passive
  Jacobian formula, source-image equality, source-rank coverage, normal
  crossings, pole order, or RLCT.
- Kill if the fixed-pivot inverse is used globally without the a.e. positivity
  argument forcing the pivot nonzero condition.
- Kill if the local-source restriction is silently dropped instead of using the
  support equality returned by the punctured-sector theorem.

## Formalisation target

New leaf module:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean
```

Target theorem:

```text
exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_marginal
```

The theorem should return the same open punctured sector `V` shape as the
source theorem and, inside that existential context, turn the two explicit
marginal assumptions into the retained-passive residual-source hypotheses for
the chart-produced source measure.
