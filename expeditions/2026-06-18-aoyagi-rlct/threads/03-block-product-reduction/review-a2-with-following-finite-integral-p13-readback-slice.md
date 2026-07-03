# Review: A2 with-following finite integral on the p.13 readback slice

Status: xhigh read-only review PASS.

Reviewer: Boole the 3rd.

Scope reviewed:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination.lean
```

The reviewer found no formalisation/math inaccuracy or overclaim in the new
slice theorem

```text
exists_open_lintegral_originalEdgeFamilyPrior_restrict_p13SourceSet_inter_readback_preimage_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_continuousAt_priorDensity_comp_sourceChart_upper
```

The theorem specializes the existing chart-piece theorem to

```text
chartPiece = p13SourceSet inter readback^{-1}(V).
```

Measurability is justified by the returned local equality

```text
sourceChart '' V = p13SourceSet inter readback^{-1}(V),
```

and the two support callbacks are just the two projections from membership in
the intersection.

The reviewer also checked that the p.13 image equality used here is local to
the returned shrink `V`, with the same `sourceChart`, `readback`, and
`p13SourceSet`, and that the reverse inclusion only applies to points in
`p13SourceSet` whose readback lands in `V`.

Boundary: no source-side neighborhood coverage, arbitrary p.13 support,
global p.13 coverage, source-rank coverage, finite atlas,
Haar/Jacobian transport, normal crossings, pole order, or RLCT.
