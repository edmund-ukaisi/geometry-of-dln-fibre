# Reproduction - A2 Case 2 Passive-theta Source-image p.13 Source-set Support

Date: 2026-07-01.

Status: pen-and-paper check completed before Lean; Lean theorem implemented and verified.

## Question

The current p.13 source-image finite-integral wrappers require both

```text
chartPiece subset sourceChart '' V
chartPiece subset p13SourceSet.
```

Can the second containment be recovered from the first for the local
passive-theta endpoint source image?

## Calculation

Let

```text
retainedData theta :=
  case2PassiveThetaEndpointRetainedData n hS hcont hnext theta eNext e

sourceChart theta :=
  case2PassiveThetaEndpointSourceChart W2 B2 n hS hcont hnext hU0 eNext e theta
```

The existing local inverse theorem returns an open set `V` such that

```text
forall theta in V, (retainedData theta).detChart.
```

For each `theta in V`, form the determinant-chart subtype

```text
{ data := retainedData theta, property := hdetV theta htheta }.
```

The named p.13 source-chart membership theorem gives

```text
paperEndpointFixedBaseRetainedPassiveP13SourceChart W2 B2 U0 hU0
  { data := retainedData theta, property := hdetV theta htheta }
  in paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet W2 B2 U0 hU0.
```

By definition of the passive-theta endpoint source chart, this is exactly

```text
sourceChart theta in p13SourceSet.
```

Therefore, if `E in sourceChart '' V`, write `E = sourceChart theta` with
`theta in V`, and the same pointwise statement proves `E in p13SourceSet`.

## Lean Target

Add to:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
```

Target theorem:

```text
exists_open_subset_measurableSet_case2PassiveThetaEndpointSourceChart_image_subset_p13SourceEdgeFamilySet
```

The theorem should return the same local open set package as

```text
exists_open_subset_continuousOn_measurableSet_case2PassiveThetaEndpointSourceChart_image_readback_leftInverse
```

and add:

```text
forall z in V, sourceChart z in p13SourceSet
forall E in sourceChart '' V, E in p13SourceSet
```

## Nonclaims

This proves only one-way support for the chart-produced local image.  It does
not prove source coverage, source-image equality, source-rank coverage,
original-prior transport, Haar or Jacobian transport, normal crossings, pole
order, or RLCT extraction.
