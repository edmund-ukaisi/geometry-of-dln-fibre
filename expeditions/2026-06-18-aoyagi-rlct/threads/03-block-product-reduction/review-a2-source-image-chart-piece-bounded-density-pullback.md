# Review - A2 Source-image Chart-piece Bounded-density Pullback

Date: 2026-07-01.

Status: PASS.

## Scope

Review target: the generic chart-piece bounded-density readback pullback lemmas
in `RetainedPassiveCase2PassiveThetaSourceImage.lean`.

## Check

The intended proof is measure bookkeeping:

```text
external.restrict chartPiece = (sourceBase.withDensity density).restrict chartPiece
density <= c  sourceBase.restrict chartPiece-a.e.
sourceBase = map sourceChart (thetaReference.restrict V)
map readback sourceBase = thetaReference.restrict V
--------------------------------------------------------------------------
map readback (external.restrict chartPiece) <= c • thetaReference.restrict V.
```

This does not require chart-piece coverage or source-rank support.  Those are
separate downstream hypotheses.

## Verification

Passed after Lean implementation:

- focused file elaboration:
  `lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean`;
- focused module build:
  `lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage`;
- aggregate elaboration: `lake env lean DLNFibre.lean`;
- full local build: `lake build DLNFibre`;
- `lean/scripts/sorries`;
- `git diff --check`;
- direct axiom probe for both public lemmas.

The direct axiom probe reports only:

```text
[propext, Classical.choice, Quot.sound]
```

## Nonclaims

This is not original/source prior transport, source-image coverage, source-rank
coverage, Haar transport, a Jacobian formula, normal crossings, pole order, or
RLCT extraction.
