# Statement Card - A2 With-Following Source-Cylinder Raw-Patch Handoff

Status: proved, build-verified, and xhigh reviewed.

## Claim

For a determinant-sector, nonzero-pivot with-following Case 2 basepoint, there
is an open shrink `V` such that every measurable p.13 chart piece supported by

```text
sourceChart '' (V inter sourceCylinder)
```

and every explicit lower source-density bound `eps <= sourceDensity` on
`baseJ.restrict V` gives a localized raw-patch domination

```text
rawHaar.restrict (rawSourceSet inter rawChart^{-1}(chartPiece))
  <= (Cdet * eps^{-1}) *
     Measure.map rawMap (coordinateSourceMeasure.restrict V)
```

for some finite scalar `Cdet`, provided `eps` is neither zero nor infinity.

## Lean Declaration

```text
exists_open_subset_rawHaar_restrict_patch_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_coordinateSourceMeasure_restrict_of_chartPiece_subset_sourceChart_image_inter_sourceCylinder_sourceDensity_lower
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

The local raw/source compatibility package shows that the raw-order endpoint
coordinates read back through the p.13 raw chart as the source chart.  The
source-cylinder support condition then gives endpoint-patch containment in the
active selected-entry endpoint image.  The already formalized
active-containment raw-patch theorem supplies finite scalar domination after
the explicit lower source-density bound is used.

## Nonclaims

No full determinant-chart Haar transport, exact raw-Haar pushforward,
Haar-scalar normalization, source-density positivity, source-image coverage,
source-rank coverage, original-prior transport, normal crossings, pole order,
or RLCT extraction is proved.

## Verification

Passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination.lean
lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination
lake build cited-audit
lake exe cited-audit
git diff --check
lean/scripts/sorries
```

Direct axiom probe reports only:

```text
[propext, Classical.choice, Quot.sound]
```

Direct `#audit_cited` classifies the theorem as FORMALISED.
