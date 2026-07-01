# Review - A2 Case 2 source-chart source-reference readback

Date: 2026-07-01.

## Verdict

PASS after focused and full Lean verification.

## Soundness Check

The theorem is measure bookkeeping for the already produced local image.  The
readback a.e.-measurability comes from the continuous injective local source
chart and its pointwise left inverse.  The measure identity is the push-pull
calculation using the left inverse almost everywhere on `thetaReference.restrict
V`.

## Boundary

The source reference is `Measure.map sourceChart (thetaReference.restrict V)`.
No original source prior, density comparison, source-image coverage,
Haar/Jacobian transport, normal crossings, pole order, or RLCT extraction is
proved.

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
The direct axiom probe reported only
`[propext, Classical.choice, Quot.sound]`.
