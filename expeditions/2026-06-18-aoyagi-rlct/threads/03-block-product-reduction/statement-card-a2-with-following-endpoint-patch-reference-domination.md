# Statement Card - A2 With-Following Endpoint-Patch Reference Domination

Status: proved, build-verified, and xhigh reviewed.

## Claim

For a determinant-sector, nonzero-pivot with-following Case 2 basepoint, there
is an open shrink `V` such that every p.13 chart piece supported by

```text
sourceChart '' (V inter sourceCylinder)
```

has a localized endpoint-patch domination

```text
rawHaar.restrict
  (rawDetChart inter rawOrderOnEndpoint^{-1}
    (rawSourceSet inter rawChart^{-1}(chartPiece)))
  <= Cdet * Measure.map Y (referenceSource.restrict V)
```

for some finite scalar `Cdet`.

## Lean Declaration

```text
exists_open_subset_rawHaar_restrict_endpointPatch_le_smul_measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_referenceSource_of_chartPiece_subset_sourceChart_image_inter_sourceCylinder
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
- chart-piece support over `sourceChart '' (V inter sourceCylinder)`.

## Proof Spine

The source-cylinder support and local raw/source compatibility prove the
endpoint patch is contained in the active selected-entry endpoint image.  The
already formalized active endpoint Haar domination theorem then supplies a
finite scalar domination by the named endpoint reference image, which is
definitionally `Measure.map Y (referenceSource.restrict V)`.

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
git diff --check
lean/scripts/sorries
```

Direct axiom probe reports only:

```text
[propext, Classical.choice, Quot.sound]
```
