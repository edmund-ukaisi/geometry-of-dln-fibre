# Review - A2 Case 2 product source-chart source-rank preservation

Date: 2026-07-01.

## Verdict

PASS after focused and full Lean verification.

## Soundness Check

The certificate theorem is a direct conversion:
retained-passive local-source membership gives recursive determinant charts,
and the existing generic constructor gives the product-reduction certificate.
The small-ball source-rank theorem then combines this certificate with the
existing passive-theta source-rank theorem and the generic product-coordinate
source-rank preservation theorem.

## Boundary

The result is one-way membership for chart-produced points.  It does not show
that every source-rank point is in the image, nor does it prove source-prior
transport, Haar/Jacobian transport, normal crossings, pole order, or RLCT.

## Verification

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
env LEAN_NUM_THREADS=3 lake env lean --stdin
```

`./scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
The direct axiom probes for the two new theorems reported only
`[propext, Classical.choice, Quot.sound]`.
