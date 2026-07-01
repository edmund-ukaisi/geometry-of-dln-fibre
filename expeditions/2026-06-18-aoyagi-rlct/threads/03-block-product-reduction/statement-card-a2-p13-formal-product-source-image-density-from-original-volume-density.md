# Statement Card: A2 p.13 formal-product source-image density from original-volume density

## Status

Proved in Lean.

## Lean theorem

```text
map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_eq_withDensity_of_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity
```

File:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13SourceMeasureBridge.lean
```

## Statement

On a measurable p.13 chart piece contained in the named p.13 source
edge-family set, if the restricted original edge-family volume is a
`withDensity` perturbation of a source reference measure, then the p.13
formal-product chart measure is the `withDensity` perturbation of the same
source reference by the scalar-multiplied density `cHaar • volumeDensity`.

The theorem exposes `cHaar : NNReal` and `c : ENNReal := cHaar`; the density in
the conclusion is `c • volumeDensity`.

## Dependencies

- p.13 formal-product/original-volume chart-piece equality:
  `map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_eq_smul_originalEdgeFamilyVolume_restrict_chartPiece`.
- Mathlib scalar density identity:
  `withDensity_smul'`.
- Restriction/scalar compatibility:
  `Measure.restrict_smul`.

## Nonclaims

The theorem does not prove the original-volume/source-reference density
identity, the source-image identity for the direct formal-product route,
source coverage, passive-theta image equality, source-rank coverage, Haar
scalar normalization, normal crossings, pole order, or RLCT extraction.
