# Review: A2 Case 2 small-ball product readout package

Date: 2026-06-30.

Reviewer: xhigh scout `Faraday the 2nd`.

## Verdict

PASS.

## Scope

The theorem

```text
exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_readout_package
```

packages five readout/source-readback facts under one small regular-coordinate
ball:

```text
regularCoordinateMap(productSourceChart(theta,u)) = u
residualCoordinateMap(productSourceChart(theta,u))
  =
residualCoordinateMap(sourceChart theta)
regularReadback(productSourceChart(theta,u)) = u
selectedInverseReadout(productSourceChart(theta,u))
  =
selectedInverseReadout(sourceChart theta)
sourceReadback(productSourceChart(theta,u)) has the canonical p.13 product fields
```

The radius is uniform in `theta` and is chosen only from determinant-unit
smallness for `ctopMatrix u`.

## Nonclaim Boundary

No accidental claim of source-image coverage, prior/Haar transport, normal
crossings, pole order, RLCT, or full passive-theta recovery was found.  The
inverse readout is explicitly the selected residual inverse readout, and the
source-readback component canonicalizes retained passive fields.

## Concern

No blocking concern.  The wrapper depends on local `let` unfolding and larger
`simpa` calls over the pointwise APIs, so harmless refactors of those APIs may
break elaboration.  This is acceptable for this packaging theorem.

## Verification

The reviewer checked `git diff --check` and a touched-Lean forbidden-marker
scan.  Controller verification additionally passed focused direct Lean check,
focused module build, full local `lake build DLNFibre`, `scripts/sorries`, and
direct axiom probe with footprint `[propext, Classical.choice, Quot.sound]`.
