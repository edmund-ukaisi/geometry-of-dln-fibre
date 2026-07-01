# Statement card: A2 Case 2 original-volume readback domination from reverse raw-source domination

Status: proved and verified.

## Lean declaration

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_restrict_rawSource_le_smul_case2PassiveTheta_rawMap
```

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadback.lean
```

## Statement

On a Case 2 passive-theta endpoint chart, there is an open local shrink
`V subset G` around `z0` such that:

- `readback (sourceChart z) = z` for `z in V`;
- `sourceChart` is injective and continuous on `V`;
- `sourceChart '' V` is measurable and lies in the p.13 source edge-family
  set.

For any theta reference measure, raw Haar measure, scalar `D`, and measurable
chart piece `C subset sourceChart '' V`, if

```text
rawHaar.restrict rawSourceSet
  <= D * Measure.map rawMap (thetaReference.restrict V),
```

then `readback` is a.e.-measurable for `originalVolume.restrict C`, and

```text
Measure.map readback (originalVolume.restrict C)
  <= ((cHaar^{-1}) * D) * thetaReference.restrict G.
```

Here `cHaar` is the fixed scalar comparing the pushed raw-order Haar measure
with `originalTupleVolume`.

## Proof inputs

- The source-chart local image/readback theorem supplies the larger shrink.
- The original-volume bridge supplies
  `originalVolume.restrict C <= (cHaar^{-1} * D) * sourceRef(V)` from the
  explicit reverse raw-source domination.
- The readback/source-chart left inverse gives
  `Measure.map readback sourceRef(V) = thetaReference.restrict V`.
- The inclusion `V subset G` weakens this to `thetaReference.restrict G`.

## Nonclaims

This does not prove the reverse raw-source domination, Haar transport,
source-image coverage, source-rank coverage, original source-prior transport,
normal crossings, pole order, or RLCT extraction.
