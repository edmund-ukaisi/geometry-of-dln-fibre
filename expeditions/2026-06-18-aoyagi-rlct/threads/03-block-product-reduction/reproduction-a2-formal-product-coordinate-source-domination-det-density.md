# A2 Case 2: formal-product domination from determinant domination and source-density lower bound

Status: pen-and-paper reproduction checked; Lean wrapper implemented.

## Question

The formal-product source-reference theorem consumes a raw-source domination
hypothesis:

```text
rawHaar.restrict rawSourceSet
  <= D * Measure.map rawMap (thetaReference.restrict Vformal).
```

Can we produce this hypothesis from the existing determinant-side reverse
domination and a lower bound on the coordinate source density, then obtain a
direct domination of the p.13 formal-product chart measure by the coordinate
source reference?

## Calculation

The existing same-shrink raw/source package gives, after shrinking inside
`Vformal`, a set `V` with `V subset Vformal` and:

```text
rawHaar.restrict rawSourceSet
  <= (Cdet * epsilon^{-1}) *
       Measure.map rawMap (coordinateSourceMeasure.restrict V).
```

It also proves the scalar is finite when:

```text
Cdet < infinity,
epsilon != 0,
epsilon != infinity.
```

The existing formal-product source-reference theorem may be applied on the
larger shrink `Vformal` with:

```text
thetaReference = coordinateSourceMeasure.restrict V,
D = Cdet * epsilon^{-1}.
```

Since `V subset Vformal`,

```text
(coordinateSourceMeasure.restrict V).restrict Vformal
  = coordinateSourceMeasure.restrict V.
```

Therefore the raw-source domination has exactly the form required by the
formal-product theorem.  For every chart piece contained in the p.13 source
set, the result is:

```text
formalProductMeasure.restrict chartPiece
  <= (Cdet * epsilon^{-1}) *
       Measure.map sourceChart (coordinateSourceMeasure.restrict V).
```

## Boundary

This removes only the reverse raw-source domination socket for the
formal-product theorem.  The determinant-side reverse domination and
source-density lower bound remain explicit hypotheses on the returned shrink.
The theorem does not construct determinant Haar transport, exact raw-Haar
pushforward, raw-Haar normalization, source-image coverage, source-rank
coverage, original source-prior transport, source-density identification,
normal crossings, pole order, or RLCT extraction.
