# Statement Card - A2 Case 2 full image prior domination from image bounds

## Expected Lean Names

```text
ae_restrict_upper_of_forall_mem

exists_open_subset_originalEdgeFamilyPrior_restrict_sourceChart_image_le_smul_sourceImageReference_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceImageDensity_image_lower_priorDensity_image_upper
```

## Statement Shape

For every open neighborhood `G` of a Case 2 passive-theta point in the
determinant sector with nonzero selected pivot, Lean returns one open
neighborhood `V` with `z0 in V` and `V subset G`.

On this same `V`, the theorem packages the existing source-chart facts:

- source-chart readback on `V`;
- `Set.InjOn sourceChart V`;
- `ContinuousOn sourceChart V`;
- `MeasurableSet (sourceChart '' V)`;
- `sourceChart '' V subset p13SourceSet`.

For every additive raw Haar measure, the theorem then proves full-image prior
domination under the determinant-side reverse domination hypothesis

```text
rawHaar.restrict rawDetChart
  <= Cdet * Measure.map Y (passiveSource.restrict V),
```

with `Cdet < infinity`, `epsilon` nonzero and finite, and pointwise image
bounds

```text
forall E in sourceChart '' V, epsilon <= sourceImageDensity E,
forall E in sourceChart '' V, density E <= Kprior.
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

- The existing full-image prior-domination theorem with a.e. source/prior
  density sockets.
- `ae_restrict_comp_lower_of_forall_image_lower` for the source-density lower
  bound.
- `ae_restrict_upper_of_forall_mem` for the prior-density upper bound.
- The returned measurability of `sourceChart '' V`.

## Nonclaims

The pointwise image bounds remain hypotheses on the returned `sourceChart '' V`.
The theorem does not prove positivity, boundedness, or concrete identification
of `sourceImageDensity`; it does not prove the prior-density upper bound.  It
does not prove determinant-chart Haar transport, exact raw-Haar pushforward,
raw-Haar normalization, source-image coverage, source-rank coverage, normal
crossings, pole order, or RLCT extraction.

The converse implications are not claimed: an a.e. bound may ignore null
points whose images still lie in `sourceChart '' V`.
