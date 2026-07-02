# A2 reproduction: with-following localized endpoint-patch readback domination

Date: 2026-07-02

## Claim

For the with-following Case 2 passive-theta source chart, let

```text
rawMap = topologyTupleEdgeRawOrder o endpointTopologyTuple,
rawOrderOnEndpoint = topologyTupleEdgeRawOrder,
rawSourceSet = topologyTupleRawOrderSourceRecursiveDetChartSet,
rawChart = paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart.
```

For a measurable p.13 chart piece `C`, the raw patch needed by that chart
piece is

```text
P := rawSourceSet inter rawChart^{-1}(C).
```

The determinant-side patch corresponding to `P` is

```text
Omega_P := rawDetChart inter rawOrderOnEndpoint^{-1}(P).
```

If

```text
rawHaar.restrict Omega_P
  <= Cdet * Measure.map Y (referenceSource.restrict V),
Cdet < infinity,
epsilon <= sourceDensity z for baseJ.restrict V-a.e. z,
epsilon != 0,
epsilon != infinity,
```

then, after shrinking inside the local source-chart/readback neighborhood,

```text
D := Cdet * epsilon^{-1}
```

is finite and

```text
map readback (originalVolume.restrict C)
  <= (((cHaar^{-1} : NNReal) : ENNReal) * D)
       * coordinateSourceMeasure.restrict G.
```

The theorem also returns a.e. measurability of the readback on
`originalVolume.restrict C`.

## Reproduction

The localized raw-image handoff applies to the patch `P` above.  Its input is
determinant reverse domination on

```text
rawDetChart inter rawOrderOnEndpoint^{-1}(P).
```

Together with the source-density lower bound this gives

```text
rawHaar.restrict P
  <= (Cdet * epsilon^{-1})
       * Measure.map rawMap (coordinateSourceMeasure.restrict V).
```

The p.13 localized chart-piece handoff then uses the two inclusions

```text
P subset rawSourceSet,
rawSourceSet inter rawChart^{-1}(C) subset P,
```

which are both immediate for this chosen `P`.  The readback package requires
the stronger target-side hypothesis

```text
C subset sourceChart '' V.
```

This supplies both `C subset p13SourceSet` and the local source-chart
left-inverse needed to pull the source reference back to the coordinate
source measure.

The p.13 original-volume bridge contributes the Haar scalar

```text
cHaar :=
  ((Measure.map rawOrderMatrixTupleEquiv rawHaar)
     .addHaarScalarFactor originalTupleVolume).
```

Hence the final scalar is

```text
(((cHaar^{-1} : NNReal) : ENNReal) * (Cdet * epsilon^{-1})).
```

The returned shrink is inside the outer set `G`, so the final domination is
lifted from `coordinateSourceMeasure.restrict V` to
`coordinateSourceMeasure.restrict G` by restriction monotonicity.

## Lean landing

Implemented in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination.lean
```

New theorem:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_endpointPatch_restrict_le_smul_case2PassiveThetaWithFollowingFactor_rawMap_sourceDensity_lower
```

## Kill conditions checked

- The theorem is with-following only.  The non-with-following determinant
  wrapper does not directly consume the localized with-following patch stack.
- The endpoint-patch domination remains an explicit hypothesis; it is not
  derived from full determinant Haar transport.
- The chart piece must be measurable and contained in the returned local
  source image for readback.
- The endpoint patch must be null-measurable for `rawHaar`.
- The lower density constant must satisfy `epsilon != 0` and
  `epsilon != infinity`, and `Cdet` must be finite.
- The inverse Haar scalar is retained explicitly; it is not set to one.
- This proves no determinant-Haar transport, source-density positivity,
  original-prior transport, source-image coverage, source-rank coverage,
  normal crossings, pole order, or RLCT extraction.
