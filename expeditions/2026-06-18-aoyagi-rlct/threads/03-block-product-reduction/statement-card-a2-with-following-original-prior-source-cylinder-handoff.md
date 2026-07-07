# Statement Card - A2 With-Following Original-Prior Source-Cylinder Handoff

Status: proved, build-verified, and xhigh reviewed.

## Claim

For a determinant-sector, nonzero-pivot with-following Case 2 basepoint, there
is an open shrink `V` such that every measurable p.13 chart piece supported by

```text
sourceChart '' (V inter sourceCylinder)
```

with an explicit lower source-density bound `eps <= sourceDensity` on
`baseJ.restrict V` and an a.e. upper prior-density bound
`density <= Kprior` on `originalVolume.restrict chartPiece` gives a localized
original-prior domination

```text
originalPrior.restrict chartPiece
  <= (ofReal Kprior *
      (((cHaar^-1 : NNReal) : ENNReal) * (Cdet * eps^{-1}))) *
     Measure.map sourceChart (coordinateSourceMeasure.restrict V)
```

for some finite scalar `Cdet`, provided `eps` is neither zero nor infinity.

## Intended Lean Declaration

```text
exists_open_subset_originalEdgeFamilyPrior_restrict_chartPiece_le_smul_coordinateSourceReference_of_chartPiece_subset_sourceChart_image_inter_sourceCylinder_sourceDensity_lower_priorDensity_upper
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
- `eps != 0` and `eps != infinity`;
- an a.e. upper bound `density <= Kprior` on
  `originalVolume.restrict chartPiece`.

## Proof Spine

Apply the original-volume source-cylinder theorem to dominate
`originalVolume.restrict chartPiece` by the coordinate-source image measure.
Then apply `originalEdgeFamilyPrior_restrict_le_smul_of_ae_le` to dominate
`originalPrior.restrict chartPiece` by `ofReal Kprior` times that restricted
original volume.  Compose the two scalar dominations.

## Nonclaims

No determinant-chart Haar transport, exact raw-Haar pushforward,
Haar-scalar normalization, source-density positivity, prior-density
boundedness, source coverage, source-rank coverage, source-prior or
original-prior transport, readback domination, finite-integral transfer,
normal crossings, pole order, or RLCT extraction is proved.

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
