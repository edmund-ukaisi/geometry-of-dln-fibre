# Review - A2 Case 2 original-volume readback domination same-shrink conditional

Date: 2026-07-01.

Status: controller review PASS; Lean verification passed.

## Checks

- The raw-Haar raw-source pushforward must remain an explicit hypothesis.
- The source-chart package, volume/source-image identity, and readback
  domination must use the same `V`.
- The domination target should be `thetaReference.restrict G`, not
  `thetaReference.restrict V`, because this is the shape consumed by the
  finite-integral wrapper with a larger theta-domain neighborhood.
- The chart-piece hypothesis should be `chartPiece subset sourceChart '' V`;
  containment in the p.13 source set should be derived.
- The theorem should only be advertised as a readback-domination adapter.

## Boundary

Passing this review does not prove raw-Haar identification, Haar transport,
source-prior transport, source coverage, normal crossings, pole order, or RLCT.

## Source/API Review

Xhigh finite-integral/API review found that the existing bounded
source-image finite-integral theorem cannot be used as a black box because it
chooses its own existential `V`.  The landed theorem instead uses the
same-witness bridge directly and then applies the direct readback-domination
adapter on that same `V`.

Xhigh source-boundary review reaffirmed that Aoyagi p.13 supplies block
algebra and regular-variable counting, not an unconditional original-volume
transport theorem.  The raw-Haar raw-source pushforward hypothesis must stay
visible.

## Verification

Focused elaboration, focused module build, full local `lake build DLNFibre`,
`lean/scripts/sorries`, `git diff --check`, and direct axiom probe passed.
The direct axiom probe reported only
`[propext, Classical.choice, Quot.sound]`.
