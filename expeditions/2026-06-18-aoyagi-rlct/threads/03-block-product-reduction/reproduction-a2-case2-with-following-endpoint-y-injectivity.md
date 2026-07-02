# Reproduction - A2 Case 2 with-following endpoint Y injectivity

Date: 2026-07-02.

Status: controller pen-and-paper reproduction before Lean implementation.

## Question

For the enlarged Case 2 endpoint map

```text
Y z =
  case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
    n hS hcont hnext z eNext e,
```

is `Y` injective on the selected-pivot-nonzero locus

```text
{z | case2PassiveThetaPivotNonzero n hS hnext z.1}?
```

Answer: yes.  This is a pointwise finite-coordinate fact.  It uses only the
active readout of the endpoint topology tuple and the elementary injectivity of
the selected-entry coordinate chart away from the pivot hyperplane.

Under the standard Polish/Borel hypotheses used by the existing local endpoint
image lemmas, the same argument also gives measurable image for every
measurable source subset contained in this locus:

```text
MeasurableSet (Y '' Ω).
```

## Source Calculation

Aoyagi's Case 2 selected-entry change of variables on PDF pp. 19-21 chooses a
successor pivot and writes the active successor block in selected-entry
coordinates.  In the Lean retained-passive model the enlarged source point is

```text
z = (theta, F)
```

where `theta` contains the passive fields and the selected-entry center
coordinates `theta.yNext`, while `F` is the following factor.  The endpoint map
`Y` builds the endpoint topology tuple after transporting indices.

There is an existing active readout theorem:

```text
endpointTopologyTupleActiveReadout n e (Y z)
  =
((z.1.1,
  SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext), z.2)
```

where

```text
pivotNext = case2PassiveThetaPivotNext n hS hnext.
```

Suppose `z` and `w` both satisfy the selected-pivot nonzero condition and
`Y z = Y w`.  Applying `endpointTopologyTupleActiveReadout n e` to the equality
gives

```text
((z.1.1, chartMap pivotNext z.1.yNext), z.2)
  =
((w.1.1, chartMap pivotNext w.1.yNext), w.2).
```

Therefore:

- the passive fields agree: `z.1.1 = w.1.1`;
- the following factors agree: `z.2 = w.2`;
- the selected-entry chart images agree:

```text
chartMap pivotNext z.1.yNext = chartMap pivotNext w.1.yNext.
```

The nonzero-locus hypotheses are exactly

```text
z.1.yNext pivotNext != 0,
w.1.yNext pivotNext != 0.
```

The existing elementary selected-entry lemma

```text
SelectedEntrySignedBox.CenterCoord.injOn_chartMap_pivot_ne_zero pivotNext
```

then gives `z.1.yNext = w.1.yNext`.  Combining the passive-field equality, the
center-coordinate equality, and the following-factor equality gives `z = w`.

For measurable images, assume `Ω` is measurable and `Ω` is contained in the
pivot-nonzero locus.  The endpoint map `Y` is continuous by the existing
continuity theorem, and the injectivity just reproduced restricts to `Ω`.
The standard Lusin-Souslin theorem used elsewhere in this thread then gives
`MeasurableSet (Y '' Ω)` under the source `BorelSpace`/`PolishSpace` and
target `OpensMeasurableSpace`/`T2Space` hypotheses.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaCFieldReadout.lean
```

New declaration:

```text
case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_injOn_pivotNonzero
measurableSet_case2PassiveThetaWithFollowingFactorEndpointSectorSet_of_subset_pivotNonzero
```

## Reproduction Verdict

This is a valid A2 endpoint-coordinate support theorem.  It is independent of
any determinant-chart Haar comparison, raw-order source chart, or measure
transport theorem.  The proof is finite-coordinate readout plus selected-entry
chart injectivity off the pivot hyperplane.  The measurable-image companion is
only the standard measurable-image consequence of continuity and this
injectivity.

## Kill Conditions

- The active readout of `Y z` must really return the passive fields, the
  selected-entry chart image of `z.1.yNext`, and the following factor `z.2`.
- The selected-pivot-nonzero predicate must match the pivot-nonzero domain of
  `SelectedEntrySignedBox.CenterCoord.injOn_chartMap_pivot_ne_zero`.
- Equality of passive fields and equality of `yNext` must reconstruct the
  `Case2PassiveTheta` component extensionally.
- The measurable-image theorem must keep the standard Polish/Borel source
  hypotheses explicit; they are not proved by this coordinate readout lemma.

## Nonclaims

No local change-of-variables formula, no Jacobian determinant theorem, no
determinant-chart Haar equality, no raw-Haar transport, no raw-order
composition, no source-image coverage beyond actual images, no formal-product
domination, no normal crossings, no pole order, and no RLCT extraction is
proved here.
