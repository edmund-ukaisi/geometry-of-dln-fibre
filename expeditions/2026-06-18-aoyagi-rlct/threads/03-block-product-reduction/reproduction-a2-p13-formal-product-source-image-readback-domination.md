# Reproduction - A2 p.13 formal-product source-image readback domination

## Boundary

This note records the elementary measure calculation formalised in

```text
map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_readback_le_smul_coordinateSourceMeasure_restrict_of_sourceImageReference_eq_withDensity_of_continuousOn_injOn
```

in `lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13ReadbackFiniteIntegral.lean`.

The result is a socket.  It does not prove the p.13 formal-product measure is a
bounded-density perturbation of the passive-theta source-image reference.  It
only proves the readback domination consequence once that bounded-density
identity and bound are supplied.

## Objects

Let `Theta` be a local passive-theta coordinate domain.  On an open measurable
piece `V`, let

```text
sourceRef(V) := Measure.map sourceChart (coordinateSourceMeasure.restrict V).
```

The p.13 formal-product chart-piece measure is

```text
muP13(chartPiece) :=
  (Measure.map
    (fun z => p13SourceChart (topologyTupleEdgeRawOrder z))
    ((m.restrict rawDetChart).withDensity
      (fun z => ENNReal.ofReal
        (retainedPassiveFormalRawOrderJacobianProductAbsDetAt z))))
    .restrict chartPiece.
```

Here `rawDetChart` is the determinant chart for the p.13 raw topology tuple,
and the density is the retained-passive formal raw-order absolute determinant.
The raw-order map is part of the definition; dropping it would attach the
Jacobian to the wrong chart.

## Assumptions

Assume:

```text
V is measurable,
chartPiece is measurable,
V subset W,
sourceChart is continuous on V,
sourceChart is injective on V,
readback (sourceChart theta) = theta for theta in V.
```

Assume also the bounded-density comparison

```text
muP13(chartPiece) = (sourceRef(V).withDensity delta).restrict chartPiece
```

and the a.e. bound

```text
delta(E) <= D
```

for `sourceRef(V).restrict chartPiece`-a.e. `E`.

## Calculation

1. By bounded-density domination on a restricted measurable piece,

```text
(sourceRef(V).withDensity delta).restrict chartPiece <= D * sourceRef(V).
```

Using the supplied equality, this gives

```text
muP13(chartPiece) <= D * sourceRef(V).
```

2. The local inverse hypotheses give readback a.e.-measurability for
`sourceRef(V)` and the exact pullback identity

```text
Measure.map readback sourceRef(V) = coordinateSourceMeasure.restrict V.
```

3. Mapping the domination in step 1 by `readback` preserves the scalar bound:

```text
Measure.map readback muP13(chartPiece)
  <= D * coordinateSourceMeasure.restrict V.
```

4. Since `V subset W`, restriction monotonicity gives

```text
coordinateSourceMeasure.restrict V <= coordinateSourceMeasure.restrict W.
```

Multiplying by the same scalar `D` yields

```text
Measure.map readback muP13(chartPiece)
  <= D * coordinateSourceMeasure.restrict W.
```

The same absolute-continuity argument gives

```text
AEMeasurable readback muP13(chartPiece).
```

## Checks

The scalar is exactly the supplied density bound `D`.  The p.13 Haar scalar
`cHaar` is not part of this theorem because the calculation does not route
through original edge-family volume.  If later one passes from `muP13` to
original volume, the already-proved inverse-Haar bridge supplies the extra
`cHaar^{-1}` factor.

## Nonclaims

The theorem does not prove the bounded-density comparison, source-image
coverage, source-rank coverage, Haar transport from raw p.13 coordinates to
passive theta coordinates, normalization of `cHaar`, normal crossings, pole
order, or RLCT extraction.
