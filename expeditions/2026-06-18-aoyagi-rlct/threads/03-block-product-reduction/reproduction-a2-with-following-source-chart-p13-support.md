# Reproduction - A2 with-following source-chart p.13 support

Date: 2026-07-02.

## Scope

This note proves a local support fact for the enlarged Case 2 passive-theta
source chart with the independent following factor:

```text
sourceChart '' V subset p13SourceSet.
```

This is one-way support for chart-produced source points.  It is not p.13
source-set coverage, p.13 image equality, source-prior transport, Haar
transport, normal crossings, pole order, or RLCT extraction.

## Objects

Let

```text
Theta = Case2PassiveThetaWithFollowingFactor ...
sourceChart : Theta -> EdgeFamily
retainedData : Theta -> RetainedPassiveNonredundantCoordinateData
```

where

```text
sourceChart z =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    (retainedData z).
```

The with-following local source-chart package already gives, after shrinking
inside the prescribed open neighborhood `G`, an open set `V` such that

```text
(retainedData z).detChart      for all z in V,
readback (sourceChart z) = z   for all z in V,
Set.InjOn sourceChart V,
ContinuousOn sourceChart V,
MeasurableSet (sourceChart '' V).
```

## Pointwise Support

For a point `z in V`, the determinant-chart proof makes

```text
detData = ⟨retainedData z, (retainedData z).detChart⟩
```

an element of the determinant-chart subtype used by the fixed-base p.13 source
chart.  The retained-passive source theorem says:

```text
paperEndpointFixedBaseRetainedPassiveP13SourceChart detData
  ∈ paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet.
```

Unfolding the with-following endpoint source chart identifies the left-hand side
with `sourceChart z`.  Therefore

```text
sourceChart z ∈ p13SourceSet
```

for every `z in V`.

## Image Support

If `E ∈ sourceChart '' V`, choose `z ∈ V` with `E = sourceChart z`.  The
pointwise support result gives `E ∈ p13SourceSet`.

Thus, after the same local shrink,

```text
sourceChart '' V subset p13SourceSet.
```

## Downstream Use

Any theorem whose hypotheses include both

```text
chartPiece subset sourceChart '' V
chartPiece subset p13SourceSet
```

can discharge the second hypothesis from the first on this shrink.  This only
removes a local support field.  It does not remove the raw-pushforward equality
or any source-prior/Haar transport hypothesis.
