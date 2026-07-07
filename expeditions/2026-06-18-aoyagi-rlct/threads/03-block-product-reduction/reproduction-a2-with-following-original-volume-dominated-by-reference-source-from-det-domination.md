# Reproduction - A2 with-following original volume dominated by reference source from determinant domination

Date: 2026-07-07.

## Claim

On the with-following Case 2 passive-theta local chart, the determinant-side
reverse domination

```text
rawHaar.restrict rawDetChart
  <= Cdet • Measure.map Y (referenceSource.restrict V)
```

implies, after shrinking around the base point, domination of the original
edge-family volume on any measurable p.13 chart piece:

```text
originalVolume.restrict chartPiece
  <= Dvol • Measure.map sourceChart (referenceSource.restrict V).
```

The chart piece must remain measurable and contained in `p13SourceSet`.

## Pen-And-Paper Check

The previous reproduction gives, on a shrink `V`, a finite local Jacobian
upper-bound scalar `CJ` such that determinant domination implies

```text
formalProductMeasure.restrict chartPiece
  <= Ddet • sourceRef,
```

where

```text
Ddet = Cdet * CJ,
sourceRef = Measure.map sourceChart (referenceSource.restrict V),
```

and `formalProductMeasure` is the raw-order formal-product measure pushed
through the p.13 raw-order source chart.

The existing p.13 original-volume bridge says that for any Haar measure
`rawHaar` on the raw tuple space, any measurable
`chartPiece subset p13SourceSet`, and any source measure `sourceRef`,

```text
formalProductMeasure.restrict chartPiece <= Ddet • sourceRef
```

implies

```text
originalVolume.restrict chartPiece
  <= (((cHaar^-1 : NNReal) : ENNReal) * Ddet) • sourceRef.
```

Here `cHaar` is the finite Haar scalar comparing the raw tuple Haar pushed
through the fixed p.13 linear equivalence with `originalTupleVolume`.

Thus the determinant-domination theorem and the p.13 original-volume bridge
compose directly.  The final scalar is

```text
Dvol = ((cHaar^-1 : NNReal) : ENNReal) * (Cdet * CJ),
```

which is finite because `Cdet < infinity`, `CJ < infinity`, and the coercion
of any `NNReal` to `ENNReal` is finite.

## Boundary

This is a consumer of the formal-product comparison.  It does not prove exact
raw-Haar pushforward, determinant Haar transport, source-image coverage,
source-rank coverage, source-prior or original-prior transport, readback
domination, normal crossings, pole order, or RLCT extraction.
