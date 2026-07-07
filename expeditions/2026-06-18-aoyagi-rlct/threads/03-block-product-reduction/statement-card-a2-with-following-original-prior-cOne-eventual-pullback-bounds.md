# Statement Card - A2 With-Following Original-Prior C-One Eventual Pullback Bounds

Status: proved, build-verified, and xhigh reviewed.

## Claim

For a determinant-sector, nonzero-pivot with-following Case 2 basepoint, if
the pulled-back source-image density is eventually bounded below by `eps` and
the pulled-back original-prior density is eventually bounded above by
`Kprior` near the basepoint, then after shrinking the direct original-prior
C-one source-support domination theorem can be applied without separate
caller-supplied a.e. density hypotheses.

The returned package still requires, when used on a chart piece:

```text
MeasurableSet chartPiece
chartPiece subset sourceChart '' V
forall E in chartPiece, cOneReadout E in signedBox
eps != 0
eps != infinity.
```

It then produces finite `Cdet` and

```text
originalPrior.restrict chartPiece
  <= (ofReal Kprior *
      (((cHaar^-1 : NNReal) : ENNReal) * (Cdet * eps^-1))) •
     Measure.map sourceChart (coordinateSourceMeasure.restrict V).
```

## Intended Lean Declaration

```text
exists_open_subset_originalEdgeFamilyPrior_restrict_chartPiece_le_smul_coordinateSourceReference_of_chartPiece_subset_sourceChart_image_cOneReadout_mem_signedBox_eventually_sourceImageDensity_comp_sourceChart_lower_priorDensity_comp_sourceChart_upper
```

in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination.lean
```

## Inputs

- the usual with-following Case 2 hypotheses;
- a base point in the determinant sector with selected pivot nonzero;
- fixed `eps`, original-prior density `density`, and `Kprior`;
- eventual lower bound for `sourceImageDensity (sourceChart z)` near `z0`;
- eventual upper bound for `density (sourceChart z)` near `z0`;
- an open ambient neighborhood `G`;
- additive Haar measure `rawHaar` on the endpoint tuple space;
- measurable chart-piece support over `sourceChart '' V`;
- pointwise C-one signed-box support on the chart piece;
- `eps != 0` and `eps != infinity`.

## Proof Spine

Intersect `G` with the common eventual event for the two pullback density
bounds.  Apply the direct original-prior C-one source-support theorem inside
that intersection.  The returned `V` lies in the event, so every point of
`sourceChart '' V` inherits the source-image density lower bound, and every
point of a chart piece contained in that image inherits the original-prior
density upper bound.  The generic restrict helpers convert these pointwise
facts into the two a.e. facts expected by the direct C-one theorem.

## Nonclaims

No C-one signed-box support for arbitrary chart pieces, source-density
positivity, prior-density boundedness from continuity, determinant-chart Haar
transport, exact raw-Haar pushforward, Haar-scalar normalization, source
coverage, source-rank coverage, source-prior or original-prior transport,
readback domination, finite-integral transfer, normal crossings, pole order,
or RLCT extraction is proved.

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
