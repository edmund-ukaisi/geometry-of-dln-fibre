# A2 Case 2: full source-image prior domination from pointwise image bounds

Status: pen-and-paper reproduction checked; Lean target implemented and xhigh
review passed.

## Question

The current full source-image prior-domination theorem returns a passive-theta
shrink `V` and proves domination of

```text
(originalEdgeFamilyPrior density).restrict (sourceChart '' V)
```

by the chart-produced source-image reference, but it asks for two
measure-theoretic hypotheses:

```text
forall-ae z with respect to baseJ.restrict V,
  epsilon <= sourceDensity z,

forall-ae E with respect to originalVolume.restrict (sourceChart '' V),
  density E <= Kprior.
```

Here

```text
sourceDensity z := sourceImageDensity (sourceChart z).
```

The image-bound wrapper should expose stronger but more geometric sufficient
hypotheses on the returned image

```text
I := sourceChart '' V:

forall E in I, epsilon <= sourceImageDensity E,
forall E in I, density E <= Kprior.
```

The conclusion and all determinant-side hypotheses should be exactly the same
as in the current full-image prior-domination theorem.

## Calculation

For the source-density lower bound, restricted measures are supported on their
restriction set.  Since `V` is measurable,

```text
forall-ae z with respect to baseJ.restrict V, z in V.
```

If `z in V`, then `sourceChart z in sourceChart '' V`; hence the pointwise
image lower bound gives

```text
epsilon <= sourceImageDensity (sourceChart z) = sourceDensity z.
```

Thus

```text
forall E in sourceChart '' V, epsilon <= sourceImageDensity E
```

implies

```text
forall-ae z with respect to baseJ.restrict V,
  epsilon <= sourceDensity z.
```

For the prior-density upper bound, the same support fact applies to the
restricted original volume.  Since `sourceChart '' V` is one of the returned
measurable facts,

```text
forall-ae E with respect to originalVolume.restrict (sourceChart '' V),
  E in sourceChart '' V.
```

Therefore

```text
forall E in sourceChart '' V, density E <= Kprior
```

implies

```text
forall-ae E with respect to originalVolume.restrict (sourceChart '' V),
  density E <= Kprior.
```

Feeding these two a.e. bounds into the already-proved full-image
prior-domination theorem gives the same finite scalar

```text
Cprior =
  ENNReal.ofReal Kprior *
    (((cHaar^{-1} : NNReal) : ENNReal) * (Cdet * epsilon^{-1}))
```

and the same domination

```text
(originalEdgeFamilyPrior density).restrict (sourceChart '' V)
  <= Cprior *
     (Measure.map sourceChart (coordinateSourceMeasure.restrict V)).restrict
       (sourceChart '' V).
```

No determinant, raw-order, or source-prior transport statement is changed.

## Boundary

This wrapper proves only that pointwise bounds on the returned image are
sufficient for the existing a.e. density sockets.  It does not prove that
`sourceImageDensity` is positive, nonzero, locally bounded, or concretely
identified with a transported density.  It does not prove that the original
prior density is bounded on the image.  It does not prove determinant-chart
Haar transport, exact raw-Haar pushforward, raw-Haar normalization,
source-image coverage, source-rank coverage, normal crossings, pole order, or
RLCT extraction.

The converse implications are not claimed: a.e. bounds may ignore null points
whose images remain in `sourceChart '' V`.
