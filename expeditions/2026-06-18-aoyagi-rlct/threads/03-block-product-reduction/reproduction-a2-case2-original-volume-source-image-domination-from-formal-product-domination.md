# Reproduction - A2 Case 2 original-volume/source-image domination from formal-product domination

Date: 2026-07-01.

## Claim

On the usual local Case 2 passive-theta source-chart shrink, suppose a
measurable chart piece lies in the actual local source image.  If the p.13
formal-product chart measure on that chart piece is dominated by a finite
scalar multiple of the chart-produced source reference

```text
sourceRef := Measure.map sourceChart (thetaReference.restrict V),
```

then the restricted original edge-family volume on the same chart piece is
dominated by the same source reference, with the inverse p.13 Haar scalar
inserted.

This is not the formal-product/source-image comparison itself.  It is the
measure bridge that turns that comparison into the original-volume domination
needed by the source-image finite-integral socket.

## Pen-And-Paper Check

Fix a local shrink `V` where the Case 2 endpoint source chart has image inside
the p.13 source edge-family set.  Let

```text
muP13 :=
  (Measure.map
    (fun z =>
      p13SourceChart (topologyTupleEdgeRawOrder z))
    ((m.restrict rawDetChart).withDensity formalJacobian)).restrict chartPiece.
```

The p.13 source-measure bridge already proves on any measurable chart piece
inside the p.13 source set:

```text
originalVolume.restrict chartPiece
  = cHaar^{-1} • muP13,
```

where `cHaar` is the tuple-side additive Haar scalar for `m`.

Assume the actual missing comparison:

```text
muP13 <= D • sourceRef.
```

Then by scalar monotonicity and composition of measure dominations,

```text
originalVolume.restrict chartPiece
  <= (cHaar^{-1} * D) • sourceRef.
```

The only geometric input used to apply the p.13 bridge is

```text
chartPiece subset sourceChart '' V
sourceChart '' V subset p13SourceSet.
```

The second inclusion is already formalized for the local Case 2 source chart.

## Boundary

This proves neither `muP13 <= D • sourceRef` nor an equality with bounded
density.  Those are still the local change-of-variables/source-coverage/lower
density target.  The result also does not identify raw Haar with the
passive-theta source image, prove source-prior transport, normalize `cHaar`,
construct normal crossings, compute pole order, or extract an RLCT.
