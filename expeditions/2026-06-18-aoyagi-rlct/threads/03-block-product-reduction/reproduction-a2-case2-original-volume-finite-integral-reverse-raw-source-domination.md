# A2 Case 2: finite integral from reverse raw-source domination

Status: checked for formalisation.

## Goal

We want the original-volume finite-integral wrapper to consume the weaker
measure comparison

```text
rawHaar.restrict rawSourceSet
  <= D * Measure.map rawMap (coordinateSourceMeasure.restrict V)
```

with `D < infinity`, rather than the exact raw-pushforward identity

```text
Measure.map rawMap (coordinateSourceMeasure.restrict V)
  = rawHaar.restrict rawSourceSet.
```

## Calculation

The direct original-volume finite-integral front end needs, for each
measurable chart piece `C`, the readback hypotheses

```text
AEMeasurable readback (originalVolume.restrict C)
```

and

```text
Measure.map readback (originalVolume.restrict C)
  <= Csource * coordinateSourceMeasure.restrict W
```

with `Csource < infinity`.

The reverse raw-source readback theorem supplies these on a same-shrink
`V subset W` from

```text
rawHaar.restrict rawSourceSet
  <= D * Measure.map rawMap (coordinateSourceMeasure.restrict V).
```

It gives

```text
Measure.map readback (originalVolume.restrict C)
  <= ((cHaar^{-1}) * D) * coordinateSourceMeasure.restrict W.
```

Thus set

```text
Csource = (cHaar^{-1}) * D.
```

This scalar is finite whenever `D < infinity`, because the inverse Haar scalar
is the coercion of an `NNReal` into `ENNReal`.

The remaining hypotheses are unchanged from the raw-pushforward finite
integral wrapper: the chart piece must be measurable, lie in the local source
set `U inter sourceStratum`, and lie in the actual image `sourceChart '' V`;
the original-prior density must be bounded above a.e. on
`originalVolume.restrict C`.

## Nonclaims

This theorem still does not prove the reverse raw-source domination.  It only
shows that the finite-integral consumer needs no exact raw-pushforward
equality once such a finite reverse domination is available.  There is still
no determinant-chart Haar transport, source-image coverage, source-rank
coverage, original source-prior transport, normal crossings, pole order, or
RLCT extraction.
