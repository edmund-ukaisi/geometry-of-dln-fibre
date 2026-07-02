# Reproduction - A2 with-following original-volume readback domination

Date: 2026-07-02.

## Scope

This note turns the with-following original-volume/source-reference domination
into a readback domination statement on the same local chart image.

It is conditional.  The raw-pushforward equality

```text
Measure.map rawMap (thetaReference.restrict V) = rawHaar.restrict rawSourceSet
```

remains a hypothesis.  Chart-piece measurability, containment in the actual
source-chart image, and containment in the p.13 source set also remain explicit.

## Objects

Let `Theta` be the enlarged Case 2 passive-theta coordinate type with the
independent following factor.  On a local open set, let

```text
sourceChart : Theta -> EdgeFamily
readback    : EdgeFamily -> Theta
rawMap      : Theta -> RawTuple
sourceRef   = Measure.map sourceChart (thetaReference.restrict V).
```

The source-chart package gives a local set `V0` on which

```text
readback (sourceChart z) = z,
Set.InjOn sourceChart V0,
ContinuousOn sourceChart V0,
MeasurableSet (sourceChart '' V0).
```

The original-volume domination theorem then shrinks inside `V0`.  Thus the
smaller set `V` inherits the left-inverse, injectivity, and continuity data by
restriction.  Its image measurability is then re-established from openness of
`V`, continuity of `sourceChart` on `V`, and injectivity of `sourceChart` on
`V`.

## Source Reference Pullback

For the smaller `V`, define

```text
sourceRef = Measure.map sourceChart (thetaReference.restrict V).
```

Because `sourceChart` is continuous on measurable `V`, it is a.e. measurable
for `thetaReference.restrict V`.  Since `readback` is a left inverse on `V` and
`sourceChart` is injective there, the standard local handoff gives

```text
AEMeasurable readback sourceRef
Measure.map readback sourceRef = thetaReference.restrict V.
```

Since `V subset G`,

```text
thetaReference.restrict V <= thetaReference.restrict G.
```

Therefore

```text
Measure.map readback sourceRef <= 1 * thetaReference.restrict G.
```

## Volume Domination Input

The with-following original-volume domination theorem gives, under the supplied
raw-pushforward equality and the chart-piece hypotheses,

```text
originalVolume.restrict chartPiece
  <= D * sourceRef,
```

where

```text
D = ((cHaar^-1 : NNReal) : ENNReal) * 1
```

and `cHaar` is the tuple-side Haar scalar from pushing raw Haar through the
p.13 raw-order matrix-tuple linear equivalence.

## Readback Transfer

Apply the generic measure handoff:

```text
readback_aemeasurable_and_map_le_smul_of_le_smul_source_measure_le
```

with

```text
mu       = originalVolume.restrict chartPiece
sourceRef = Measure.map sourceChart (thetaReference.restrict V)
thetaRef  = thetaReference.restrict G
C         = D
Csource   = 1.
```

It yields

```text
AEMeasurable readback (originalVolume.restrict chartPiece)
Measure.map readback (originalVolume.restrict chartPiece)
  <= (D * 1) * thetaReference.restrict G.
```

The Lean theorem simplifies the harmless final `* 1`, leaving the same scalar
as the upstream original-volume domination theorem:

```text
((cHaar^-1 : NNReal) : ENNReal) * 1.
```

## Boundary

This proves readback a.e. measurability and readback domination only for
measurable p.13 chart pieces contained in the actual with-following source
chart image, and only under the raw-pushforward equality.  It proves no
raw-Haar transport, determinant-chart Haar theorem, source-image coverage,
source-prior or original-prior transport, density lower-bound removal, normal
crossings, pole order, or RLCT extraction.
