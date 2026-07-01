# A2 p.13 formal-product source-image density from original-volume density

## Pen-and-paper reproduction

Fix a measurable p.13 chart piece `C` contained in the named p.13 source
edge-family set.  The established chart-piece comparison is

```text
mu_formal = cHaar • (originalEdgeFamilyVolume.restrict C).
```

Assume a source-reference density identity for original edge-family volume:

```text
originalEdgeFamilyVolume.restrict C =
  (sourceRef.withDensity volumeDensity).restrict C.
```

Then

```text
mu_formal
  = cHaar • (sourceRef.withDensity volumeDensity).restrict C
  = (sourceRef.withDensity (cHaar • volumeDensity)).restrict C.
```

The last equality is `withDensity_smul'` plus restriction commuting with scalar
multiplication.  The scalar is the finite `NNReal` Haar comparison scalar,
viewed in `ENNReal`.

## Lean target

`OriginalEdgeFamilyP13SourceMeasureBridge.lean` proves:

```text
map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_eq_withDensity_of_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity
```

## Boundary

This converts a supplied original-volume density identity into a formal-product
density identity.  It does not prove the original-volume density identity,
source-image coverage, passive-theta image equality, Haar scalar normalization,
normal crossings, pole order, or RLCT extraction.
