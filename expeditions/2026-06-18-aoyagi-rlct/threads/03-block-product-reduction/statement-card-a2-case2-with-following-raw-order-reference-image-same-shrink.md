# Statement card - A2 with-following raw-order reference image same-shrink package

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawOrderReference.lean
```

Names:

```text
case2PassiveThetaWithFollowingFactorRawOrderReferenceImageMeasure
exists_open_subset_case2PassiveThetaWithFollowingFactorRawOrderReferenceImage_same_shrink_package
```

## Claim

For the enlarged Case 2 passive-theta source with independent following factor,
there is a local open shrink `V` around a determinant-sector, nonzero-pivot base
point such that the named raw-order image measure

```text
Measure.map rawMap (referenceSource.restrict V)
```

simultaneously satisfies:

- support on the raw-order source-recursive determinant chart;
- domination for every source measure dominated by the enlarged reference
  source;
- compatibility with the named endpoint reference image under the raw-order map;
- compatibility between the raw-order p.13 source chart and the direct enlarged
  endpoint source chart;
- raw-density transport through the same raw/source-chart handoff.

## Inputs

- the usual `W2`, `B2`, `n`, `S`, `J`, `hS`, `hcont`, `hnext`, `U0`, `hU0`,
  endpoint equivalences `eNext` and `e`;
- a base point `z0` in the enlarged determinant sector;
- nonzero selected pivot at `z0.1`;
- the residual weight `Rres`;
- an open neighborhood `G` with `z0 in G`;
- standard measurable/open/Borel/T2 instances for the source, raw tuple, and
  edge-family targets required by the existing bridge.

## Output

The theorem returns one open set `V` with `z0 in V` and `V subset G`.  With

```text
referenceSource =
  case2PassiveThetaWithFollowingFactorReferenceSourceMeasure ...

rawMap z =
  topologyTupleEdgeRawOrder
    (case2PassiveThetaWithFollowingFactorEndpointTopologyTuple ... z)

rawOrderReferenceImage =
  case2PassiveThetaWithFollowingFactorRawOrderReferenceImageMeasure ... V
```

it returns:

```text
rawOrderReferenceImage.restrict rawSourceSet = rawOrderReferenceImage
```

and, for `sourceMeasure <= d * referenceSource`,

```text
Measure.map rawMap (sourceMeasure.restrict V)
  <= d * rawOrderReferenceImage.
```

It also returns:

```text
Measure.map Phi endpointReferenceImage = rawOrderReferenceImage

Measure.map rawChart rawOrderReferenceImage
  =
Measure.map sourceChart (referenceSource.restrict V)
```

and the weighted version:

```text
Measure.map rawChart (rawOrderReferenceImage.withDensity rawDensity)
  =
Measure.map sourceChart
  ((referenceSource.withDensity
    (fun theta => rawDensity (rawMap theta))).restrict V).
```

## Dependencies

- `case2PassiveThetaWithFollowingFactorReferenceSourceMeasure`;
- `case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure`;
- `exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_readback_leftInverse`;
- continuity of the enlarged endpoint topology-tuple map;
- continuity of `topologyTupleEdgeRawOrder` on the determinant chart;
- `map_le_smul_map_of_le_smul_aemeasurable`;
- `measure_map_rawChart_restrict_withDensity_comp_eq_of_twoStage_restrict`.

## Nonclaims

No raw Haar measure is constructed.  No determinant-chart Haar equality,
Jacobian determinant formula, local change-of-variables theorem, source-prior
transport, source-image coverage, formal-product domination, normal crossings,
pole order, or RLCT extraction is proved.
