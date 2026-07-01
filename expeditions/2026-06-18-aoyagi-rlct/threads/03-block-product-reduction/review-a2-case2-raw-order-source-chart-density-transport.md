# Review - A2 Case 2 raw-order source-chart density transport

Date: 2026-07-01.

## Verdict

PASS after focused and full Lean verification.

## Soundness Check

The concrete theorem is a conditional measure-transport bridge.  It uses the
existing relative Case 2 raw-order/source-chart wrapper to obtain the local
open set `V`, the pointwise equality

```text
rawChart (rawMap theta) = sourceChart theta,
```

and the already-proved two-stage pushforward equality.  The new generic
measure helper then moves a raw density through `rawMap` using
`withDensity` and `restrict_withDensity`.

## Boundary

The theorem does not identify

```text
Measure.map rawMap (thetaReference.restrict V)
```

with determinant-chart Haar measure, raw-order Haar measure, original
edge-family volume, or an original/source prior.  Those remain separate
frontier statements.  It also does not prove source-image coverage,
source-rank coverage, normal crossings, pole order, or RLCT extraction.

## Verification

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.LocalMeasureHandoff
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_axioms_probe.lean
```

`./scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
The direct axiom probe reported only
`[propext, Classical.choice, Quot.sound]`.
