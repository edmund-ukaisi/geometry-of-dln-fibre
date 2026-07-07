# Statement Card - A2 With-Following Original-Prior C-One Continuous Pullback Bounds

Status: proved, build-verified, and xhigh reviewed.

## Claim

For a determinant-sector, nonzero-pivot with-following Case 2 basepoint,
continuity of the pulled-back source-image density and pulled-back
original-prior density, together with strict basepoint inequalities, supplies
the eventual density bounds needed by the direct original-prior C-one
domination theorem.

The returned domination package still requires chart-piece measurability,
support in `sourceChart '' V`, pointwise C-one signed-box support, and
`eps != 0`, `eps != infinity` when it is used.

## Intended Lean Declaration

```text
exists_open_subset_originalEdgeFamilyPrior_restrict_chartPiece_le_smul_coordinateSourceReference_of_chartPiece_subset_sourceChart_image_cOneReadout_mem_signedBox_of_continuousAt_sourceImageDensity_comp_sourceChart_strict_lower_continuousAt_priorDensity_comp_sourceChart_strict_upper
```

in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination.lean
```

## Inputs

- the usual with-following Case 2 hypotheses;
- a base point in the determinant sector with selected pivot nonzero;
- fixed `eps`, original-prior density `density`, and `Kprior`;
- `ContinuousAt (fun z => sourceImageDensity (sourceChart z)) z0`;
- `eps < sourceImageDensity (sourceChart z0)`;
- `ContinuousAt (fun z => density (sourceChart z)) z0`;
- `density (sourceChart z0) < Kprior`;
- an open ambient neighborhood `G`;
- the chart-piece and Haar inputs inherited by the returned domination
  package.

## Proof Spine

Use
`eventually_sourceImageDensity_comp_lower_priorDensity_comp_upper_of_continuousAt`
to obtain the two eventual pullback bounds.  Then call
`exists_open_subset_originalEdgeFamilyPrior_restrict_chartPiece_le_smul_coordinateSourceReference_of_chartPiece_subset_sourceChart_image_cOneReadout_mem_signedBox_eventually_sourceImageDensity_comp_sourceChart_lower_priorDensity_comp_sourceChart_upper`.

## Nonclaims

No continuity of the pullbacks is proved.  No source-density positivity or
finiteness, prior-density nonnegativity, positivity, or boundedness without
the explicit strict basepoint hypotheses, C-one signed-box support for
arbitrary chart pieces, determinant-chart Haar transport, exact raw-Haar
pushforward, Haar normalization, source coverage, source-rank coverage,
source-prior or original-prior transport, readback domination,
finite-integral transfer, normal crossings, pole order, or RLCT extraction is
proved.

## Verification

Passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination.lean
lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination
lake exe cited-audit
lean/scripts/sorries
git diff --check
```

`lean/scripts/sorries` reports `0 sorry`, `0 #exit`, `0 native_decide`, and
only the existing three cited axioms.  The citation audit reports
`UNACCOUNTED=0`, `CITED=2`, and `LOCATION=0`.  A direct axiom probe reports
only:

```text
[propext, Classical.choice, Quot.sound]
```

Direct `#audit_cited` classifies the theorem as FORMALISED.
