# Reproduction - A2 Original Edge-Family Raw-Order Edge-Volume Bridge

Date: 2026-07-01.

Status: pen-and-paper check before Lean.  This is the fixed-basis
edge-family-volume lift of the raw-order tuple measure bridge.

## Question

The preceding slice proves, for

```text
L := rawOrderMatrixTupleContinuousLinearEquiv e,
```

that a restricted raw-coordinate Haar measure maps to

```text
c • (originalTupleVolume d).restrict (L '' S),
```

where

```text
c := (Measure.map L m).addHaarScalarFactor (originalTupleVolume d).
```

If `b` is a fixed basis family and

```text
T := tupleToEdgeFamily b,
```

what is the honest pushed measure on continuous edge-family space?

## Calculation

First, `T` is the inverse of the fixed-basis matrix-coordinate equivalence

```text
edgeFamilyMatrixTupleContinuousLinearEquiv b.
```

Therefore, for any tuple set `A`,

```text
Measure.map T ((originalTupleVolume d).restrict A)
  = (originalEdgeFamilyVolume b).restrict (T '' A).
```

This is just the restriction compatibility of a measurable equivalence:
push forward the restricted measure and use

```text
T ⁻¹' (T '' A) = A.
```

Second, apply this to

```text
A := L '' S.
```

The tuple-side bridge gives

```text
Measure.map L (m.restrict S)
  = c • (originalTupleVolume d).restrict (L '' S).
```

Mapping both sides by `T` gives

```text
Measure.map (T ∘ L) (m.restrict S)
  = c • (originalEdgeFamilyVolume b).restrict (T '' (L '' S)).
```

Since

```text
T '' (L '' S) = (T ∘ L) '' S,
```

the final form is

```text
Measure.map (fun y => T (rawOrderMatrixTuple e y)) (m.restrict S)
  = c • (originalEdgeFamilyVolume b).restrict
      ((fun y => T (rawOrderMatrixTuple e y)) '' S).
```

For the formal-product retained-passive chart, compose the existing raw-order
change-of-variables theorem with

```text
ψ y := T (rawOrderMatrixTuple e y).
```

The result is the same scalar-restricted edge-family volume on the image of
the raw source-recursive determinant chart.

## Lean Target

Extend:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyRawOrderMeasureBridge.lean
```

with:

```text
map_tupleToEdgeFamily_originalTupleVolume_restrict_eq_originalEdgeFamilyVolume_restrict_image
map_rawOrderMatrixTuple_tupleToEdgeFamily_restrict_eq_smul_originalEdgeFamilyVolume_restrict_image
map_formalProduct_rawOrderMatrixTuple_tupleToEdgeFamily_eq_smul_originalEdgeFamilyVolume_restrict_image
```

## Kill Conditions

- If `tupleToEdgeFamily b` is not the measurable inverse of the matrix
  coordinate readout, the restriction transport step is invalid.
- If the scalar is identified with `1` without a separate normalization
  theorem, the result overclaims.
- If the theorem is cited as source coverage or as a statement that the
  restricted source-image measure is Haar, the result overclaims.
- If the theorem is used as normal-crossing or RLCT extraction, the result
  overclaims.

## Nonclaims

No theorem here proves source coverage, chart-image equality with the full
original source, scalar normalization to `1`, restricted Haar structure,
normal crossings, pole order, or RLCT extraction.
