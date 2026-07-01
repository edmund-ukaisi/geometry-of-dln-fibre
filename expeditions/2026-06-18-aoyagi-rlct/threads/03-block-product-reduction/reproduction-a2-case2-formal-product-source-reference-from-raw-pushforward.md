# Reproduction - A2 Case 2 formal-product source-reference identity from raw pushforward

Date: 2026-07-01.

Status: pen-and-paper reproduction before Lean formalisation.

## Question

Assume the local passive-theta raw-order map has the raw-source pushforward

```text
Measure.map rawMap (thetaReference.restrict V)
=
rawHaar.restrict rawSourceSet.
```

What does this imply about the p.13 formal-product chart measure on a
measurable p.13 source-set chart piece, relative to the chart-produced source
reference?

## Calculation

Let

```text
sourceRef := Measure.map sourceChart (thetaReference.restrict V).
```

The local Case 2 two-stage chart identity gives

```text
Measure.map rawChart (Measure.map rawMap (thetaReference.restrict V))
=
sourceRef.
```

By the raw-pushforward hypothesis, the left side is

```text
Measure.map rawChart (rawHaar.restrict rawSourceSet).
```

The p.13 formal-product chart-measure theorem gives

```text
formalProductMeasure =
(Measure.map rawChart (rawHaar.restrict rawSourceSet)).restrict p13SourceSet.
```

Combining these identities gives

```text
formalProductMeasure = sourceRef.restrict p13SourceSet.
```

Restricting to a measurable `chartPiece subset p13SourceSet` gives

```text
formalProductMeasure.restrict chartPiece =
sourceRef.restrict chartPiece.
```

Finally, constant-density reweighting by `1` is the identity:

```text
sourceRef.restrict chartPiece =
(sourceRef.withDensity (fun _ => 1)).restrict chartPiece.
```

Therefore

```text
formalProductMeasure.restrict chartPiece =
(sourceRef.withDensity (fun _ => 1)).restrict chartPiece,
```

with a.e. bound `1 <= 1`.

## Boundary

The raw-pushforward identity is still an explicit hypothesis.  This calculation
does not derive it from Aoyagi p.13.  It only packages the consequence needed by
the formal-product source-reference finite-integral socket once that raw-source
pushforward has been supplied.

This does not prove full raw Haar transport, source-image coverage,
source-rank coverage, original source-prior transport, scalar normalization,
normal crossings, pole order, or RLCT extraction.  The density `1` is only the
identity density relative to the chart-produced source reference.
