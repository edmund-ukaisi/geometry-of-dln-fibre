# A2 p.13 formal-product domination from original-volume source-image density

## Pen-and-paper reproduction

Fix a p.13 chart piece `C` contained in the named p.13 source edge-family set.
The established p.13 source-set bridge gives, on `C`,

```text
mu_formal = cHaar • (originalEdgeFamilyVolume.restrict C).
```

Assume the original edge-family volume on `C` has a bounded source-image
density:

```text
originalEdgeFamilyVolume.restrict C =
  (sourceRef.withDensity volumeDensity).restrict C,
volumeDensity <= D   a.e. for sourceRef.restrict C.
```

The local density bound gives

```text
(sourceRef.withDensity volumeDensity).restrict C <= D • sourceRef.
```

Therefore

```text
mu_formal <= cHaar • (D • sourceRef) = (cHaar * D) • sourceRef.
```

No inverse Haar scalar appears in this forward direction.  The inverse scalar
appears only in the reverse direction, when bounding original volume from a
formal-product source-reference identity.

## Lean target

`OriginalEdgeFamilyP13SourceMeasureBridge.lean` proves:

```text
map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_le_smul_sourceMeasure_of_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_bounded
```

The theorem is an elementary consumer of the existing chart-piece comparison
and `restrict_withDensity_le_smul_of_ae_le`.

## Boundary

This does not prove the original-volume/source-image density identity, the
density bound, source coverage, chart-image equality, Haar normalization,
normal crossings, pole order, or RLCT extraction.
