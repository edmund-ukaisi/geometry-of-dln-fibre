# Reproduction - A2 Case 2 passive theta coordinate domain

Date: 2026-06-30.

Status: pen-and-paper check for a first Lean coordinate-domain slice.

## Question

What is the smallest full passive-sector object that can replace the reduced
selected-entry section as the future source for determinant-chart measure
transport?

The reduced selected-entry chart only varies the successor residual center
coordinates

```text
yNext : {p // p in case2ResidualBlockPivotEntries n S (J+1)} -> R.
```

The retained p.13 chart also has passive coordinates.  In the existing Lean
passive datum these are precisely

```text
A1passive, F2, A3passive, Ctop, F3.
```

Thus the first construction should package these passive coordinates together
with `yNext`, then feed them through the already-proved finite retained-passive
datum

```text
case2PostPivotSelectedEntryRetainedPassiveDataWithPassive.
```

## Pen-And-Paper Calculation

For the Case 2 post-pivot two-edge retained-passive datum, the active residual
factors `C` are still the two matrices obtained from Aoyagi's displayed
post-pivot block calculation:

```text
F2 = -A1^{-1} A2,
F3 = -A3 A1^{-1},
C4 = -A3 A1^{-1} A2 + A4.
```

The selected-entry coordinates determine only the successor residual block in
those active `C` factors.  They do not determine the retained passive fields.
Therefore the full local coordinate vector for this stage is

```text
theta = (A1passive, F2, A3passive, Ctop, F3, yNext).
```

The determinant-chart condition for the retained-passive tuple is also
coordinatewise: it asks for `Ctop` and every passive `A1` block to have unit
determinant.  No condition on the selected-entry residual center coordinates is
needed for determinant-chart membership.  The nonzero selected pivot is a
separate punctured-sector condition used by selected-entry inverse readout.

Thus the elementary Lean slice is:

```text
Case2PassiveTheta
case2PassiveThetaRetainedData
case2PassiveThetaTopologyTuple
case2PassiveThetaDetSector
case2PassiveThetaPivotNonzero
```

with the determinant statements:

```text
theta in case2PassiveThetaDetSector
  -> (case2PassiveThetaRetainedData theta).detChart

theta in case2PassiveThetaDetSector
  -> case2PassiveThetaTopologyTuple theta in topologyTupleDetChartSet.
```

Endpoint transport should have parallel definitions and determinant lemmas,
because the local p.13 source chart lives after transport into the endpoint
complement indices.

## Source Boundary

Aoyagi pp. 10-13 support the block coordinate construction and the p.13
retained-passive product-difference chart.  The present slice uses only this
finite matrix-coordinate algebra and the already-formalised retained-passive
coordinate datum.  It does not use the quiver-based paper or quiver Lean
results.

## Nonclaims

This slice does not prove determinant-chart Haar transport, source-prior
transport, full passive-sector measure equality, finite-scalar domination,
bounded-density domination, source-image equality, source-rank coverage,
normal crossings, pole order, or RLCT extraction.  It is only a full coordinate
domain and determinant-chart membership layer for later measure work.
