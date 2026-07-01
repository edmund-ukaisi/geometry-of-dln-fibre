# Statement Card: A2 p.13 formal-product domination from original-volume source-image density

## Status

Proved in Lean.

## Lean theorem

```text
map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_le_smul_sourceMeasure_of_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_bounded
```

File:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13SourceMeasureBridge.lean
```

## Statement

On a measurable p.13 chart piece contained in the named p.13 source
edge-family set, if the restricted original edge-family volume is a
`withDensity` perturbation of a source reference measure and that density is
locally a.e. bounded by `D`, then the p.13 formal-product chart measure is
dominated by the same source reference with scalar `(cHaar : ENNReal) * D`.

## Dependencies

- p.13 formal-product/original-volume chart-piece comparison:
  `map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_le_smul_sourceMeasure_of_originalEdgeFamilyVolume_restrict_chartPiece_le_smul`.
- Local bounded-density domination:
  `restrict_withDensity_le_smul_of_ae_le`.

## Nonclaims

The theorem does not prove the source-image density identity, the density
bound, source coverage, passive-theta image equality, source-rank coverage,
Haar scalar normalization, normal crossings, pole order, or RLCT extraction.
