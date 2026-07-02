# Reproduction - A2 with-following constant-density handoff to original-volume domination

Date: 2026-07-02.

## Scope

This note composes two already-proved measure handoffs for the enlarged
Case 2 passive-theta chart with the independent following factor.

The result is conditional.  It does not remove the raw-pushforward equality

```text
Measure.map rawMap (thetaReference.restrict V) = rawHaar.restrict rawSourceSet.
```

It also keeps chart-piece measurability, actual source-image containment, and
p.13 source-set containment explicit.

## Objects

Let

```text
sourceChart : Theta -> EdgeFamily
rawMap      : Theta -> RawTuple
```

be the with-following endpoint source chart and its raw-order map on the local
Case 2 coordinate type `Theta`.  Let

```text
sourceRef = Measure.map sourceChart (thetaReference.restrict V).
```

Let `formalProductMeasure` be the p.13 formal-product chart measure obtained
from raw Haar on the raw determinant chart with the retained-passive formal
raw-order Jacobian density.  Let `originalVolume` be the fixed-base original
edge-family Haar volume, and let

```text
cHaar =
  ((Measure.map L rawHaar).addHaarScalarFactor (originalTupleVolume d)).
```

Here `L` is the raw-order matrix-tuple continuous linear equivalence used in
the p.13 source-measure bridge.

## Existing Inputs

The with-following constant-density handoff gives, after one local shrink,

```text
formalProductMeasure.restrict chartPiece
  = (sourceRef.withDensity (fun _ => 1)).restrict chartPiece

and

(fun _ => 1) <= 1  a.e. under sourceRef.restrict chartPiece.
```

Its hypotheses include:

```text
MeasurableSet chartPiece
chartPiece subset sourceChart '' V
chartPiece subset p13SourceSet
Measure.map rawMap (thetaReference.restrict V) = rawHaar.restrict rawSourceSet.
```

This is the same constant-density identity that the
`A2Case2FormalProductSourceImagePieceContract` constructor packages into the
record form.  The Lean proof uses the identity directly rather than invoking
the record eliminator, because the surrounding concrete theorem introduces
`EdgeFamily` through local `let` aliases and the direct route avoids
proof-irrelevant typeclass-alias friction.

The p.13 source-measure bridge says that any domination

```text
formalProductMeasure.restrict chartPiece <= D • sourceRef
```

implies

```text
originalVolume.restrict chartPiece
  <= (((cHaar⁻¹ : NNReal) : ENNReal) * D) • sourceRef.
```

This is a pure measure comparison on the p.13 source chart.  It does not say
that the source image covers the p.13 source set or that the raw-pushforward
equality is automatic.

## Composition

Apply the with-following constant-density handoff with the supplied
raw-pushforward equality and p.13 chart-piece containment.  The theorem
statement also keeps the actual source-image containment
`chartPiece subset sourceChart '' V`, which is needed by downstream local
readback uses even though this particular measure comparison only uses the
p.13 containment.

The p.13 bridge then yields

```text
originalVolume.restrict chartPiece
  <= ((((cHaar⁻¹ : NNReal) : ENNReal) * 1) • sourceRef).
```

We keep the displayed scalar as `invHaar * 1` in the Lean statement to match
the bridge output and avoid a non-load-bearing simplification lemma.

## Boundary

This proves only a conditional with-following original-volume domination
from the constant-density formal-product/source-reference handoff.  It proves
no raw-Haar transport, determinant-chart Haar theorem, source-image coverage,
source-prior transport, density lower-bound removal, normal crossings, pole
order, or RLCT.
