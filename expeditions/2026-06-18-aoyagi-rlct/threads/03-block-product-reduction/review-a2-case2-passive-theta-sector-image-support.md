# Review - A2 Case 2 passive theta sector-image support

Date: 2026-06-30.

## Verdict

PASS.

Two xhigh read-only reviews checked the slice before banking:

- Source/scope reviewer `Nietzsche` returned PASS for the sector-image
  support target and FAIL/low priority for another generic domination wrapper.
- Lean/API reviewer `Beauvoir` returned PASS for the measure-support theorem
  shape, with minor API hygiene recommendations.

## Source And Scope Review

`Nietzsche` checked that the smaller sector-image target is the correct next
piece of passive-sector infrastructure.  The target names the image of the
full `Case2PassiveTheta` endpoint topology-tuple map and proves support of a
restricted pushforward on that image.  This moves toward a later exact or
dominated passive-sector measure theorem without pretending to prove
Haar/source-prior transport.

The review rejected a competing generic `withPassive` domination socket as the
next frontier step: it would add another wrapper while leaving the passive
sector image, exact/dominated sector measure comparison, and source-prior
transport fields unchanged.

## Lean/API Review

`Beauvoir` checked the proof shape for the support theorem:

```text
nu = Measure.map Y (thetaMeasure.restrict Omega)
sectorSet = Y '' Omega
```

Since `thetaMeasure.restrict Omega` is concentrated on `Omega`, the mapped
measure is concentrated on `sectorSet`.  The proof correctly uses
`ae_restrict_mem`, `ae_map_iff`, and `Measure.restrict_eq_self_of_ae_mem`.

The review emphasized two API boundaries:

- keep image-sector definitions in `RetainedPassiveCase2PassiveSector.lean`,
  which is the coordinate/topology file;
- keep the measure-support theorem in
  `RetainedPassiveCase2PassiveThetaSourceMeasure.lean`.

It also confirmed that image measurability should stay explicit: continuous
images of measurable sets are not generally measurable in this API.

## Verification

Controller checks before banking:

```text
lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSector.lean
lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceMeasure
lake env lean -E warning DLNFibre.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
```

All listed checks passed when run from the local `lean/` directory, except
`git diff --check`, which was run from the repository root.  The full build
replayed only pre-existing warning noise from unrelated modules.
`./scripts/sorries` reported:

```text
Summary: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

Direct axiom probe for the public theorem reports:

```text
[propext, Classical.choice, Quot.sound]
```

## Nonclaims

This slice does not prove exact passive-sector Haar transport,
determinant-chart Haar transport, raw-order Haar transport, source-prior
comparison, finite-scalar domination, bounded-density comparison,
source-image equality, source-rank coverage, normal crossings, pole order, or
RLCT extraction.  It only names the passive theta endpoint sector image and
proves support of a restricted chart-produced pushforward on that image.
