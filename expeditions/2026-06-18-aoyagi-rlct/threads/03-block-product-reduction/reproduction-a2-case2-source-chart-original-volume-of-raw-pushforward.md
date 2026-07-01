# Reproduction - A2 Case 2 source-chart original-volume identity from raw pushforward

Date: 2026-07-01.

Status: pen-and-paper check before Lean formalisation.

## Question

Suppose the local passive-theta coordinate measure has already been chosen so
that the raw-order map has the exact local raw-source pushforward

```text
Measure.map rawMap (thetaReference.restrict V)
=
rawHaar.restrict rawSourceSet.
```

What source-side measure does the concrete passive-theta endpoint source chart
produce?

## Calculation

On the local Case 2 determinant/pivot sector, the existing raw-order wrapper
gives

```text
rawChart (rawMap theta) = sourceChart theta       for theta in V.
```

The density-transport bridge applied with raw density `1` gives

```text
Measure.map rawChart
  ((Measure.map rawMap (thetaReference.restrict V)).withDensity 1)
=
Measure.map sourceChart
  ((thetaReference.withDensity (fun _ => 1)).restrict V).
```

Using `withDensity_one`, this reduces to

```text
Measure.map rawChart (Measure.map rawMap (thetaReference.restrict V))
=
Measure.map sourceChart (thetaReference.restrict V).
```

Now insert the explicit raw-pushforward hypothesis:

```text
Measure.map sourceChart (thetaReference.restrict V)
=
Measure.map rawChart (rawHaar.restrict rawSourceSet).
```

The p.13 source-measure bridge already proves

```text
Measure.map rawChart (rawHaar.restrict rawSourceSet)
=
cHaar • originalEdgeFamilyVolume.restrict p13SourceSet.
```

Therefore

```text
Measure.map sourceChart (thetaReference.restrict V)
=
cHaar • originalEdgeFamilyVolume.restrict p13SourceSet.
```

For a measurable chart piece contained in `p13SourceSet`, restriction gives

```text
(Measure.map sourceChart (thetaReference.restrict V)).restrict chartPiece
=
cHaar • originalEdgeFamilyVolume.restrict chartPiece.
```

The p.13 raw-order-to-original-volume theorem supplies `cHaar > 0`, hence
`cHaar != 0`.  Inverting the scalar measure identity gives

```text
originalEdgeFamilyVolume.restrict chartPiece
=
cHaar^-1 •
  (Measure.map sourceChart (thetaReference.restrict V)).restrict chartPiece.
```

Since constant-density reweighting by `cHaar^-1` is scalar multiplication of
the measure,

```text
originalEdgeFamilyVolume.restrict chartPiece
=
  ((Measure.map sourceChart (thetaReference.restrict V)).withDensity
    (fun _ => cHaar^-1)).restrict chartPiece.
```

The bounded-density side condition needed downstream is the reflexive a.e.
bound `cHaar^-1 <= cHaar^-1`.

## Boundary

The raw-pushforward hypothesis is the remaining hard local measure statement.
This reproduction does not prove it.  It only shows that once the pushforward
of the restricted theta reference along the passive-theta raw map is assumed
equal to `rawHaar.restrict rawSourceSet`, the concrete source chart lands in
the original-volume source reference already formalised for the raw-order
p.13-coordinate chart.

This is independent of the normal-crossing-to-RLCT cited boundary and does not
prove source-image coverage, source-rank coverage, pole order, or RLCT
extraction.
