# Statement Card - A2 p.13 Formal-product to Original-volume Domination

## Claim

On any measurable chart piece contained in the named p.13 source edge-family
set, a supplied domination of the p.13 formal-product chart measure by a source
reference measure implies domination of the restricted original edge-family
volume by the same source reference, with the inverse tuple-side Haar scalar
multiplying the bound.

Public Lean names:

```text
originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceMeasure_of_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_le_smul_sourceMeasure

originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceMeasure_of_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_eq_withDensity_bounded
```

## Inputs Used

- measurable `chartPiece`;
- containment of `chartPiece` in the named p.13 source edge-family set;
- the already-proved inverse-scalar p.13 formal-product/original-volume
  comparison;
- either a supplied formal-product/source-reference domination, or a supplied
  bounded-density identity and density bound for the formal-product measure.

## Output

```text
originalEdgeFamilyVolume.restrict chartPiece <= (c^{-1} * D) • sourceRef
```

where `c` is the tuple-side Haar scalar.

## Nonclaims

No proof of the supplied formal-product/source-reference comparison, no
passive-theta source-image equality, no source-prior transport, no source
coverage, no scalar normalization, no normal crossings, no pole order, and no
RLCT extraction.
