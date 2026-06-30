# Statement Card - A2 passive-theta source-image measurability

Date: 2026-06-30.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
```

Main theorem:

```text
exists_open_subset_measurableSet_case2PassiveThetaEndpointSourceChart_image_readback_leftInverse
```

Expected output:

```text
Given:
  z0 in determinant sector
  selected pivot nonzero at z0
  G open and z0 in G

Produce:
  open V
  z0 in V
  V subset G
  forall z in V, readback (sourceChart z) = z
  Set.InjOn sourceChart V
  MeasurableSet (sourceChart '' V)
```

## Inputs Used

- `exists_open_case2PassiveThetaEndpointSourceChart_readback_leftInverse`.
- `continuous_case2PassiveThetaEndpointTopologyTuple`.
- `case2PassiveThetaEndpointTopologyTuple_mem_detChartSet`.
- `continuous_case2PassiveThetaEndpointRetainedData`.
- `continuous_paperEndpointFixedBaseRetainedPassiveP13SourceChart`.
- `MeasurableSet.image_of_continuousOn_injOn`.

## Mathematical Meaning

The theorem creates an actual measurable source-side chart image for the
full passive-theta endpoint chart.  It is a prerequisite for later restricting
or comparing an external/original source measure on the target source
edge-family space.

## Nonclaims

- No source-rank local coverage.
- No source-image equality beyond `sourceChart '' V` itself.
- No original source-prior domination or equality.
- No determinant-chart Haar/raw-order Haar transport.
- No normal crossings, pole order, or RLCT extraction.
