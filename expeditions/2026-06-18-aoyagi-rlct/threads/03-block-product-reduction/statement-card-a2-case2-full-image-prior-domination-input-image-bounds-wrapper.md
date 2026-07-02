# Statement Card - A2 Case 2 full image prior domination from input-image bounds

## Expected Lean Name

```text
exists_open_subset_originalEdgeFamilyPrior_restrict_sourceChart_image_le_smul_sourceImageReference_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceImageDensity_input_image_lower_priorDensity_input_image_upper
```

## Statement Shape

For every open neighborhood `G` of a Case 2 passive-theta point in the
determinant sector with nonzero selected pivot, Lean returns one open
neighborhood `V` with `z0 in V` and `V subset G`.

On this same `V`, the theorem packages:

- source-chart readback on `V`;
- `Set.InjOn sourceChart V`;
- `ContinuousOn sourceChart V`;
- `MeasurableSet (sourceChart '' V)`;
- `sourceChart '' V subset p13SourceSet`.

For every additive raw Haar measure, the theorem proves the same full-image
prior domination as the returned-image-bound wrapper, but its density sockets
are stated on the caller's input image:

```text
forall E in sourceChart '' G, epsilon <= sourceImageDensity E,
forall E in sourceChart '' G, density E <= Kprior.
```

The determinant-side reverse domination hypothesis remains on the returned
`V`:

```text
rawHaar.restrict rawDetChart
  <= Cdet * Measure.map Y (passiveSource.restrict V).
```

The conclusion is the finite scalar bound

```text
Cprior < infinity
```

and the measure domination

```text
(originalEdgeFamilyPrior density).restrict (sourceChart '' V)
  <= Cprior *
     (Measure.map sourceChart (coordinateSourceMeasure.restrict V)).restrict
       (sourceChart '' V),
```

where

```text
Cprior =
  ENNReal.ofReal Kprior *
    (((cHaar^{-1} : NNReal) : ENNReal) * (Cdet * epsilon^{-1})).
```

## Inputs Used

- The existing returned-image-bound full prior wrapper.
- The returned containment `V subset G`.
- The elementary image containment `sourceChart '' V subset sourceChart '' G`.

## Nonclaims

The pointwise bounds on `sourceChart '' G` remain hypotheses.  The theorem
does not prove that the input image is measurable, open, or convenient as a
source-side neighborhood.  It does not prove positivity, boundedness, or
concrete identification of `sourceImageDensity`; it does not prove the prior
density upper bound.  It does not prove determinant-chart Haar transport,
exact raw-Haar pushforward, raw-Haar normalization, source-image coverage,
source-rank coverage, normal crossings, pole order, or RLCT extraction.
