# Statement Card - A2 Case 2 full image prior domination from eventual pullback bounds

## Expected Lean Name

```text
exists_open_subset_originalEdgeFamilyPrior_restrict_sourceChart_image_le_smul_sourceImageReference_of_detHaar_restrict_le_smul_endpointTopologyTuple_eventually_sourceImageDensity_comp_sourceChart_lower_priorDensity_comp_sourceChart_upper
```

## Statement Shape

For a Case 2 passive-theta point `z0` in the determinant sector with nonzero
selected pivot, fix `epsilon`, `density`, and `Kprior`.  If the two pullback
density bounds hold eventually near `z0`,

```text
forall-eventually z in nhds z0,
  epsilon <= sourceImageDensity (sourceChart z),

forall-eventually z in nhds z0,
  density (sourceChart z) <= Kprior,
```

then Lean returns one open neighborhood `V` with `z0 in V`.

On this same `V`, the theorem packages:

- source-chart readback on `V`;
- `Set.InjOn sourceChart V`;
- `ContinuousOn sourceChart V`;
- `MeasurableSet (sourceChart '' V)`;
- `sourceChart '' V subset p13SourceSet`.

For every additive raw Haar measure, the determinant-side reverse domination
hypothesis remains on the returned `V`:

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

- The input-image-bound full prior wrapper.
- Mathlib's `eventually_nhds_iff`, applied to the conjunction of the two
  eventual pullback bounds.
- The elementary image-witness step: if `E in sourceChart '' G`, choose
  `z in G` with `E = sourceChart z`.

## Nonclaims

The eventual pullback bounds remain hypotheses.  The shrink `V` is chosen
after `epsilon`, `density`, `Kprior`, and those two eventual hypotheses are
fixed; the theorem does not give one `V` uniform in all future density bounds.

The theorem does not prove continuity, positivity, boundedness, or concrete
identification of `sourceImageDensity`; it does not prove the prior density
upper bound.  It does not prove determinant-chart Haar transport, exact
raw-Haar pushforward, raw-Haar normalization, source-image coverage,
source-rank coverage, normal crossings, pole order, or RLCT extraction.
