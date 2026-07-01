# Review - A2 Source-image Chart-piece Density Readback Domination to W

Date: 2026-07-01.

Status: PASS after Lean implementation and verification.

## Scope

Review target: the generic `V subset W` chart-piece bounded-density readback
domination lemmas and the p.13 original edge-family volume specialization.

## Check

The intended proof is measure bookkeeping:

```text
external.restrict chartPiece = (sourceBase.withDensity density).restrict chartPiece
density <= c over sourceBase.restrict chartPiece
sourceBase = map sourceChart (thetaReference.restrict V)
map readback sourceBase = thetaReference.restrict V
V subset W
----------------------------------------------------------------------------
AEMeasurable readback (external.restrict chartPiece)
map readback (external.restrict chartPiece) <= c • thetaReference.restrict W.
```

Absolute continuity gives the a.e.-measurability transfer, and restriction
monotonicity gives the passage from `V` to `W`.

## Verification

Passed:

- focused file elaborations for
  `DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean`
  and
  `DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13ReadbackFiniteIntegral.lean`;
- focused module builds for
  `DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage`
  and
  `DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyP13ReadbackFiniteIntegral`;
- aggregate `lake env lean DLNFibre.lean`;
- full local `lake build DLNFibre`;
- `lean/scripts/sorries`;
- `git diff --check`;
- direct axiom probe.

The direct axiom probe reports only
`[propext, Classical.choice, Quot.sound]` for the two generic lemmas and the
p.13 specialization.

## Nonclaims

This is not original/source density transport, source-image coverage,
source-rank coverage, Haar transport, a Jacobian formula, normal crossings,
pole order, or RLCT extraction.
