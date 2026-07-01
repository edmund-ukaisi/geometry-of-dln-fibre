# Review - A2 p.13 Original-prior Volume Source-image Density Finite Integral

Date: 2026-07-01.

Status: PASS; local controller checks passed.

## Scope

Review target:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolumeSourceImageReference_eq_withDensity_bounded_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

The theorem is a structured consumer of the previously proved source-image
reference finite-integral wrapper.  Its final chart-piece handler replaces the
arbitrary hypothesis

```text
originalVolume.restrict chartPiece <= D • sourceRef
```

with a restricted-volume density identity

```text
originalVolume.restrict chartPiece =
  (sourceRef.withDensity volumeDensity).restrict chartPiece
```

and the local a.e. bound `volumeDensity <= D` over `sourceRef.restrict
chartPiece`.

## Check

The proof derives the old domination hypothesis by applying
`restrict_withDensity_le_smul_of_ae_le` to `sourceRef` and `chartPiece`, then
rewrites by the supplied density identity.  It then calls the existing
source-image reference finite-integral wrapper.  This direction is correct:
the theorem does not infer the density identity or the density bound.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13ReadbackFiniteIntegral.lean` passed.
- `lake build DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyP13ReadbackFiniteIntegral` passed.
- `lake env lean DLNFibre.lean` passed.
- Full local `lake build DLNFibre` passed.
- `lean/scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- `git diff --check` passed.
- Direct axiom probe reported only `[propext, Classical.choice, Quot.sound]`.

## Nonclaims

The theorem does not prove the source-image density identity, prove the density
bound, identify a global passive-theta image, prove source coverage, prove
chart-image equality, normalize Haar scalars, construct normal crossings,
compute pole order, extract an RLCT, or prove global original-prior
integrability beyond the supplied local chart piece.
