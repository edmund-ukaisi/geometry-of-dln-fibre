# Statement Card - A2 p.13 Source-Set Measure Bridge

## Claim

The raw-order edge-family restricted measure bridge can be rewritten with the
public p.13 fixed-base retained-passive source chart and its named source
edge-family set.

For the p.13 raw-order source chart `sourceChart`, raw source set `T`, and
named source edge-family set `sourceSet`, Lean proves:

```text
Measure.map sourceChart (m.restrict T)
= c • (originalEdgeFamilyVolume b).restrict sourceSet.
```

It also proves the formal-product Jacobian version:

```text
Measure.map (fun z => sourceChart (topologyTupleEdgeRawOrder z))
  ((m.restrict detChart).withDensity formalProductAbsDet)
= c • (originalEdgeFamilyVolume b).restrict sourceSet.
```

The scalar `c` is the tuple-side full-space Haar scalar comparing
`Measure.map (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv W B U0) m`
with `originalTupleVolume d`.

## Public Lean Names

```text
paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_eq_tupleToEdgeFamily_rawOrderMatrixTuple
map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_restrict_eq_smul_originalEdgeFamilyVolume_restrict_sourceEdgeFamilySet
map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_eq_smul_originalEdgeFamilyVolume_restrict_sourceEdgeFamilySet
```

## Inputs Used

- `edgeFamilyMatrixTuple_p13FinBasis_rawOrderSourceChart_eq_rawOrderMatrixTuple`;
- `tupleToEdgeFamily_edgeFamilyMatrixTuple`;
- `image_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_eq_sourceEdgeFamilySet`;
- the generic raw-order edge-family measure bridge;
- the existing retained-passive local Jacobian source-set theorem and support
  theorem from `RetainedPassiveLocalJacobianMeasure`.

## Proof Shape

1. Prove source-chart pointwise equality with `tupleToEdgeFamily ∘
   rawOrderMatrixTuple` on the raw source chart.
2. Use `Measure.map_congr` under `m.restrict T`.
3. Rewrite the image using the existing p.13 source-set image theorem.
4. For the formal-product statement, compose the existing local Jacobian
   source-set theorem with the restricted source-set comparison.

## Nonclaims

This is not source-rank coverage, full source coverage, restricted Haar
structure, scalar normalization to `1`, normal crossings, pole order, or RLCT
extraction.
