# Reproduction - A2 Original Edge-Family Raw-Order Measure Bridge

Date: 2026-07-01.

Status: pen-and-paper check before Lean. This is a restricted-pushforward
measure comparison after the raw-order coordinate bridge. It is not a theorem
that a restricted chart measure is Haar.

## Question

Let `L` be the full-space continuous linear equivalence from raw-order
retained-passive coordinates to original matrix tuple coordinates:

```text
L y := rawOrderMatrixTuple e y.
```

If `m` is an additive Haar measure on the full raw tuple space, what is the
honest comparison between

```text
Measure.map L (m.restrict S)
```

and the original tuple coordinate volume?

## Calculation

First use only the measurable equivalence property of `L`.  Since `L` is
bijective and measurable with measurable inverse,

```text
Measure.map L (m.restrict S)
  = (Measure.map L m).restrict (L '' S).
```

This is the standard `MeasurableEquiv.restrict_map` identity with
`L ⁻¹' (L '' S) = S`.

Second compare full-space Haar measures on the original tuple coordinate
space.  The pushed full measure

```text
Measure.map L m
```

is Haar because `L` is a continuous linear equivalence and `m` is Haar.  The
measure `originalTupleVolume d` is also Haar.  By uniqueness of additive Haar
measure, there is the canonical positive Haar scalar

```text
c := (Measure.map L m).addHaarScalarFactor (originalTupleVolume d)
```

such that

```text
Measure.map L m = c • originalTupleVolume d.
```

Restricting this full-space equality to `L '' S` gives

```text
Measure.map L (m.restrict S)
  = c • (originalTupleVolume d).restrict (L '' S).
```

No assertion is made that `m.restrict S`, `Measure.map L (m.restrict S)`, or
`(originalTupleVolume d).restrict (L '' S)` is Haar.  The scalar is a
full-space Haar scalar, then the equality is restricted.

For the retained-passive raw-order source chart, the existing formal-product
Jacobian change-of-variables theorem says

```text
Measure.map topologyTupleEdgeRawOrder
  ((m.restrict detChart).withDensity formalProductAbsDet)
= m.restrict rawSourceSet.
```

Composing both sides with `L` and applying the restricted comparison above
at `S := rawSourceSet` gives

```text
Measure.map (fun z => L (topologyTupleEdgeRawOrder z))
  ((m.restrict detChart).withDensity formalProductAbsDet)
= c • (originalTupleVolume d).restrict (L '' rawSourceSet).
```

## Lean Target

Add:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyRawOrderMeasureBridge.lean

map_rawOrderMatrixTuple_restrict_eq_smul_originalTupleVolume_restrict_image
map_formalProduct_rawOrderMatrixTuple_eq_smul_originalTupleVolume_restrict_image
```

## Kill Conditions

- If `L` is not a measurable equivalence on the full raw tuple space, the
  `restrict_map` step is invalid.
- If `Measure.map L m` is not a full-space additive Haar measure, the scalar
  comparison with `originalTupleVolume` is invalid.
- If the existing formal-product Jacobian COV target is not exactly
  `m.restrict rawSourceSet`, the composed theorem is mistyped.
- If the scalar is silently asserted to be `1`, the theorem overclaims the
  normalization.

## Nonclaims

No theorem here proves that a restricted raw-source, determinant-chart, or
source-chart measure is Haar. No theorem identifies the scalar with `1`. No
theorem compares with `originalEdgeFamilyVolume` on continuous edge families,
proves source-rank coverage, gives a chart-piece readback domination, proves
normal crossings, pole order, or RLCT extraction.
