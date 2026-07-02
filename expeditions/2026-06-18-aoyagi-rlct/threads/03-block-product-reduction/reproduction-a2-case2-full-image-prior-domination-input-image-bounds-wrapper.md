# A2 Case 2: full source-image prior domination from input-image bounds

Status: pen-and-paper reproduction checked; Lean target implemented and xhigh
review passed.

## Question

The image-bound full prior wrapper asks for pointwise bounds on the returned
image

```text
sourceChart '' V.
```

This is correct but slightly awkward for applications: the caller chooses an
open neighborhood `G` before the theorem returns `V`.  Since the returned
package always includes

```text
V subset G,
```

a stronger and more usable sufficient condition is to assume the pointwise
bounds on the known input image

```text
sourceChart '' G.
```

The goal is to expose a wrapper whose density sockets are

```text
forall E in sourceChart '' G, epsilon <= sourceImageDensity E,
forall E in sourceChart '' G, density E <= Kprior,
```

while the conclusion remains domination on the smaller returned image
`sourceChart '' V`.

## Calculation

Let `V` be the shrink returned by the existing image-bound wrapper.  It
satisfies

```text
V subset G.
```

Therefore

```text
sourceChart '' V subset sourceChart '' G.
```

Indeed, if `E in sourceChart '' V`, then there is `z in V` with
`E = sourceChart z`.  Since `V subset G`, the same `z` witnesses
`E in sourceChart '' G`.

Thus a pointwise source-density lower bound on the input image,

```text
forall E in sourceChart '' G, epsilon <= sourceImageDensity E,
```

implies the returned-image lower bound required by the existing wrapper:

```text
forall E in sourceChart '' V, epsilon <= sourceImageDensity E.
```

The same containment converts the pointwise prior-density upper bound:

```text
forall E in sourceChart '' G, density E <= Kprior
```

implies

```text
forall E in sourceChart '' V, density E <= Kprior.
```

Feeding these two bounds into the image-bound wrapper gives the same finite
scalar

```text
Cprior =
  ENNReal.ofReal Kprior *
    (((cHaar^{-1} : NNReal) : ENNReal) * (Cdet * epsilon^{-1}))
```

and the same conclusion

```text
(originalEdgeFamilyPrior density).restrict (sourceChart '' V)
  <= Cprior *
     (Measure.map sourceChart (coordinateSourceMeasure.restrict V)).restrict
       (sourceChart '' V).
```

## Boundary

This theorem still proves only a sufficient-condition wrapper.  It does not
prove that such bounds hold on `sourceChart '' G`, nor does it prove that
there is a convenient source-side open set containing `sourceChart '' G`.
It does not prove positivity, boundedness, or concrete identification of
`sourceImageDensity`, and it does not prove the original prior-density upper
bound.

It does not prove determinant-chart Haar transport, exact raw-Haar
pushforward, raw-Haar normalization, source-image coverage, source-rank
coverage, normal crossings, pole order, or RLCT extraction.
