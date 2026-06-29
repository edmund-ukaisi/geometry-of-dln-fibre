# A2 retained-passive chart-produced punctured-sector passive-product residual source

## Scope

This note reproduces the next measure handoff after the residual-source socket

```text
exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_marginal.
```

The new input is not another Aoyagi coordinate calculation.  The Aoyagi p.13
retained-passive product-difference coordinates and the selected-entry
punctured-sector readout are already reproduced in the preceding cards.  The
new step is the elementary measure calculation for the concrete coordinate
domain measure

```text
sourceMeasure = passiveMeasure.prod weightedBox,
```

where `weightedBox` is the selected-entry signed box with Aoyagi's
selected-pivot source density.  The calculation shows that the residual
marginal after restricting to the chosen punctured sector is dominated by the
unrestricted selected-entry weighted box marginal.  The selected-entry
finite-integral theorem then supplies the two marginal hypotheses required by
the residual-source socket.

## Objects

Fix the Case 2 passive selected-entry data from the punctured-sector theorem.
Let

```text
center = case2ResidualBlockPivotEntries n S (J + 1),
pivotNext = (J + 2, J + 2) in center,
X = eta x (center -> R).
```

For radii `Rres : center -> R` with `0 < Rres i`, set

```text
signedBox =
  Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),

weightedBox =
  signedBox.withDensity
    (fun y : center -> R =>
      ENNReal.ofReal
        (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y)),

sourceMeasure = passiveMeasure.prod weightedBox.
```

Assume finite passive mass:

```text
passiveMeasure Set.univ < infinity.
```

For `t : R`, assume

```text
0 <= t,
2 * t < card(center.erase pivotNext.1) + 1.
```

The selected-entry signed-box theorem gives

```text
(A) weightedBox-a.e. y,
      0 < SelectedEntrySignedBox.CenterCoord.residual pivotNext y,

(B) integral over weightedBox of
      ENNReal.ofReal ((SelectedEntrySignedBox.CenterCoord.residual pivotNext y)^(-t))
    is finite.
```

The residual-source socket returns an open determinant-and-pivot-nonzero sector
`V subset X`, with `z0 in V`, and defines

```text
mu = Measure.map sourceChart (sourceMeasure.restrict V),
marginal = Measure.map Prod.snd (sourceMeasure.restrict V).
```

The target is to prove the socket's two marginal hypotheses for this concrete
`marginal`, then apply the socket conclusion:

```text
mu.restrict localSource = mu,
mu.restrict localSource-a.e. E, 0 < residualSquare(E),
residualNegPowerIntegrableOn localSource mu t.
```

## Marginal domination after sector restriction

The key point is domination, not equality.  Since restriction only decreases a
measure,

```text
(passiveMeasure.prod weightedBox).restrict V
  <= passiveMeasure.prod weightedBox.
```

Mapping by the measurable projection `Prod.snd` preserves this inequality:

```text
Measure.map Prod.snd ((passiveMeasure.prod weightedBox).restrict V)
  <= Measure.map Prod.snd (passiveMeasure.prod weightedBox).
```

The product marginal is the scalar multiple of the second factor:

```text
Measure.map Prod.snd (passiveMeasure.prod weightedBox)
  = passiveMeasure Set.univ • weightedBox.
```

Therefore

```text
marginal <= passiveMeasure Set.univ • weightedBox.
```

No equality after restriction is asserted.  The open sector `V` may depend on
the passive and selected-entry coordinates, so its second-coordinate marginal
can be strictly smaller than the unrestricted product marginal.

## Positivity transfer

Let

```text
P(y) := 0 < SelectedEntrySignedBox.CenterCoord.residual pivotNext y.
```

The selected-entry theorem gives `weightedBox`-a.e. `P`.  The domination above
implies absolute continuity of `marginal` with respect to
`passiveMeasure Set.univ • weightedBox`, hence with respect to `weightedBox`
up to a scalar multiple.  The local helper

```text
ae_of_measure_le_smul
```

therefore gives

```text
marginal-a.e. y, P(y).
```

This is the first marginal hypothesis required by the residual-source socket.

The case `passiveMeasure Set.univ = 0` is harmless: the marginal is then
dominated by the zero measure, so the a.e. statement is vacuous and the source
pushforward is correspondingly zero on the selected sector.  No positive
passive mass is needed, only finite mass for the integral transfer.

## Finite-integral transfer

Set

```text
g(y) =
  ENNReal.ofReal
    ((SelectedEntrySignedBox.CenterCoord.residual pivotNext y)^(-t)).
```

The selected-entry theorem gives

```text
integral weightedBox g < infinity.
```

From

```text
marginal <= passiveMeasure Set.univ • weightedBox
```

and

```text
passiveMeasure Set.univ < infinity,
```

the local domination helper

```text
lintegral_lt_top_of_measure_le_smul
```

gives

```text
integral marginal g < infinity.
```

This is the second marginal hypothesis required by the residual-source socket.

## Socket application

Apply

```text
exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_marginal
```

with

```text
sourceMeasure = passiveMeasure.prod weightedBox.
```

It chooses the open sector `V`.  The domination calculation above is then
performed for that `V`, proving the two marginal hypotheses from the
selected-entry weighted-box theorem and finite passive mass.  Feeding these
into the socket proves the retained-passive p.13 residual-source positivity and
negative-power integrability for

```text
mu = Measure.map sourceChart ((passiveMeasure.prod weightedBox).restrict V).
```

## Kill conditions

- Kill if the proof states
  `Measure.map Prod.snd ((passiveMeasure.prod weightedBox).restrict V) =
  passiveMeasure Set.univ • weightedBox`; only domination follows from an
  arbitrary sector restriction.
- Kill if the theorem drops the finite passive-mass hypothesis while still
  transferring finite integrals by scalar domination.
- Kill if the theorem claims determinant-chart Haar transport, raw/source Haar
  transport, external/original source-prior transport, a passive Jacobian
  formula, source-image equality, source-rank coverage, normal crossings, pole
  order, or RLCT.
- Kill if the selected-entry theorem is applied to the chart-map image measure
  instead of the raw `weightedBox`; the residual-source socket's marginal
  hypotheses are raw selected-entry residual-coordinate hypotheses.
- Kill if the theorem is described as proving the marginal hypotheses for an
  arbitrary source measure.  The proof uses the concrete product source
  measure `passiveMeasure.prod weightedBox`.

## Formalisation target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean
```

Target theorem:

```text
exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_passiveProductMeasure_finiteMass
```

The theorem should return the same open punctured sector shape as the socket,
with `sourceMeasure` specialized to the passive product weighted-box measure,
and it should conclude the retained-passive residual-source hypotheses without
leaving the marginal positivity/integrability fields explicit.
