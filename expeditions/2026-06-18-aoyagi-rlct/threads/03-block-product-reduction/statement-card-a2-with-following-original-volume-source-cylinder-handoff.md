# Statement Card - A2 With-Following Original-Volume Source-Cylinder Handoff

Status: proved, build-verified, and xhigh reviewed.

## Claim

For a determinant-sector, nonzero-pivot with-following Case 2 basepoint, there
is an open shrink `V` such that every measurable p.13 chart piece supported by

```text
sourceChart '' (V inter sourceCylinder)
```

and every explicit lower source-density bound `eps <= sourceDensity` on
`baseJ.restrict V` gives a localized original-volume domination

```text
originalVolume.restrict chartPiece
  <= (((cHaar^-1 : NNReal) : ENNReal) * (Cdet * eps^{-1})) *
     Measure.map sourceChart (coordinateSourceMeasure.restrict V)
```

for some finite scalar `Cdet`, provided `eps` is neither zero nor infinity.

## Intended Lean Declaration

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_coordinateSourceReference_of_chartPiece_subset_sourceChart_image_inter_sourceCylinder_sourceDensity_lower
```

in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination.lean
```

## Inputs

- the usual with-following Case 2 hypotheses;
- a base point in the determinant sector with selected pivot nonzero;
- an open ambient neighborhood `G`;
- additive Haar measure `rawHaar` on the endpoint tuple space;
- measurable chart-piece support over `sourceChart '' (V inter sourceCylinder)`;
- an a.e. lower bound `eps <= sourceDensity` on `baseJ.restrict V`;
- `eps != 0` and `eps != infinity`.

## Proof Spine

Run the local p.13 source-image shrink to recover
`chartPiece subset p13SourceSet` from the public source-cylinder support.
Then apply the formal-product source-cylinder theorem to get

```text
formalProductMeasure.restrict chartPiece
  <= (Cdet * eps^{-1}) *
     Measure.map sourceChart (coordinateSourceMeasure.restrict V).
```

The p.13 original-volume bridge converts this into original-volume domination
with the extra inverse Haar scalar `((cHaar^-1 : NNReal) : ENNReal)`.

## Nonclaims

No determinant-chart Haar transport, exact raw-Haar pushforward,
Haar-scalar normalization, source-density positivity, source coverage,
source-rank coverage, original-prior transport, readback domination, normal
crossings, pole order, or RLCT extraction is proved.

## Verification

Passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination.lean
lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination
lake exe cited-audit
git diff --check
lean/scripts/sorries
```

Direct axiom probe reports only:

```text
[propext, Classical.choice, Quot.sound]
```

Direct `#audit_cited` classifies the theorem as FORMALISED.
