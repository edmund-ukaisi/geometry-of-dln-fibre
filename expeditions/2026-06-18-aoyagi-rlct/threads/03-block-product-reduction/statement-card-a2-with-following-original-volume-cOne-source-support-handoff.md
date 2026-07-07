# Statement Card - A2 With-Following Original-Volume C-One Source-Support Handoff

Status: proved, build-verified, and xhigh reviewed.

## Claim

For a determinant-sector, nonzero-pivot with-following Case 2 basepoint, there
is an open shrink `V` such that every measurable p.13 chart piece supported by

```text
sourceChart '' V
```

and satisfying the pointwise signed-box condition

```text
cOneReadout E in signedBox
```

is covered by the source-cylinder support needed for direct original-volume
domination.  With the same explicit lower source-density bound as the
source-cylinder theorem, one obtains finite `Cdet` and

```text
originalVolume.restrict chartPiece
  <= (((cHaar^-1 : NNReal) : ENNReal) * (Cdet * eps^{-1})) *
     Measure.map sourceChart (coordinateSourceMeasure.restrict V).
```

## Intended Lean Declaration

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_coordinateSourceReference_of_chartPiece_subset_sourceChart_image_cOneReadout_mem_signedBox_sourceDensity_lower
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
- measurable chart-piece support over `sourceChart '' V`;
- pointwise C-one signed-box support on the chart piece;
- an a.e. lower bound `eps <= sourceDensity` on `baseJ.restrict V`;
- `eps != 0` and `eps != infinity`.

## Proof Spine

First obtain an outer source-chart shrink with readback left-inverse,
injectivity, continuity, measurable image, and p.13 image support.  Run the
direct source-cylinder original-volume theorem inside that outer shrink.  The
inner shrink inherits the local source-chart facts, and the C-one support
bridge converts

```text
chartPiece subset sourceChart '' V
forall E in chartPiece, cOneReadout E in signedBox
```

into

```text
chartPiece subset sourceChart '' (V inter sourceCylinder).
```

Then apply the direct source-cylinder original-volume package unchanged.

## Nonclaims

No C-one support for arbitrary chart pieces, determinant-chart Haar transport,
exact raw-Haar pushforward, Haar-scalar normalization, source-density
positivity, source coverage, source-rank coverage, original-prior transport,
readback domination, finite-integral transfer, normal crossings, pole order,
or RLCT extraction is proved.

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
