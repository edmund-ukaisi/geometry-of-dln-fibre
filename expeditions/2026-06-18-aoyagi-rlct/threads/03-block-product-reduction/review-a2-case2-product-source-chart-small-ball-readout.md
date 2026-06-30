# Review - A2 Case 2 product source chart small-ball readout

Date: 2026-06-30.

## Verdict

PASS after focused and full Lean verification.

## Soundness Check

The theorem is a direct specialization of the generic small-ball
regular/residual readout theorem.  It introduces no new determinant argument:
the radius and determinant-unit guarantee come from the existing
regular-suspension API.

## Source Fidelity

This matches the elementary p.13 local-coordinate calculation.  Aoyagi's
regular variables are only valid in a determinant chart near `Ctop = I`; the
small-ball theorem packages that chart condition as a radius around the origin
in the regular Euclidean coordinates.

## Boundary

The theorem is local and eventual along a named source stratum.  It does not
prove chart image coverage, a full readback to `(theta,u)`, source-prior
transport, Haar transport, a Jacobian formula, normal crossings, pole order,
or RLCT extraction.

## Verification

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_product_small_ball_axioms.lean
```

`./scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
The direct axiom probe for the new theorem reported only
`[propext, Classical.choice, Quot.sound]`.
