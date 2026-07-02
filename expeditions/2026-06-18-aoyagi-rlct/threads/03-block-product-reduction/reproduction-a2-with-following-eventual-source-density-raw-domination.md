# Reproduction - A2 with-following eventual source-density raw domination

Date: 2026-07-02.

## Scope

The latest with-following raw-domination theorem assumes the lower
source-density bound in its measure-theoretic form:

```text
ae z with respect to baseJ.restrict V,
  eps <= sourceImageDensity (sourceChart z).
```

This note prepares the smaller topological adapter that replaces that a.e.
input by an eventual pullback lower bound near the base point:

```text
forall-eventually z in nhds z0,
  eps <= sourceImageDensity (sourceChart z).
```

The determinant-side reverse domination remains a hypothesis:

```text
rawHaar.restrict rawDetChart
  <= Cdet * Measure.map Y (referenceSource.restrict V).
```

The theorem should not identify `sourceImageDensity`, prove it positive, or
compare the endpoint reference image with determinant Haar.

## Pen-and-paper calculation

Let:

```text
sourceDensity z = sourceImageDensity (sourceChart z).
baseJ = referenceSource.withDensity jacobianDensity.
coordinateSourceMeasure = baseJ.withDensity sourceDensity.
```

Assume:

```text
forall-eventually z in nhds z0, eps <= sourceDensity z.
```

By the neighborhood characterization of `nhds`, choose an open set `H`
containing `z0` such that:

```text
z in H -> eps <= sourceDensity z.
```

The caller also supplies an open neighborhood `G` of `z0`.  Work inside:

```text
G' = G inter H.
```

Apply the existing with-following reference-source reverse raw-domination
theorem to `G'`.  It returns an open set `V` with:

```text
z0 in V,  V subset G'.
```

Therefore `V subset G`, and for every `z in V` we have `z in H`, hence:

```text
eps <= sourceDensity z.
```

Since `V` is open, it is measurable.  The standard restriction fact gives:

```text
ae z with respect to baseJ.restrict V, z in V.
```

Thus:

```text
ae z with respect to baseJ.restrict V, eps <= sourceDensity z.
```

This is exactly the a.e. hypothesis consumed by the existing lower-density
raw-domination theorem.  The conclusion is unchanged:

```text
(Cdet * eps^-1) < infinity
```

and

```text
rawHaar.restrict rawSourceSet
  <= (Cdet * eps^-1) *
       Measure.map rawMap (coordinateSourceMeasure.restrict V).
```

## Boundary

This theorem proves only the conversion:

```text
eventual pullback lower bound -> a.e. lower bound on the returned shrink.
```

It does not prove the eventual lower bound, continuity of the pullback
density, a strict basepoint lower value, or any concrete formula for
`sourceImageDensity`.

It also does not prove determinant-chart Haar domination/equality, exact
raw-Haar pushforward, source-prior/original-prior transport, p.13 coverage or
source-rank coverage, normal crossings, pole order, or RLCT extraction.

## Lean proof plan

The proof should live in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawImageHandoff.lean
```

The target theorem should call:

```text
exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_coordinateSourceMeasure_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
```

after shrinking the input neighborhood to the intersection of the caller's
`G` and the open neighborhood extracted from the eventual bound.

The only new proof step is:

```text
filter_upwards [ae_restrict_mem hVopen.measurableSet] with z hzV
```

followed by the pointwise lower bound on the extracted neighborhood.
