# Review - A2 Case 2 product source chart regular/residual readout

Date: 2026-06-30.

## Verdict

PASS after focused and full Lean verification.

## Soundness Check

The theorem is a direct specialization of the generic product-coordinate
readout theorem.  The `M := 0` specialization matches the concrete Case 2
endpoint types:

```text
Fin (0+3) = Fin 3
Fin (0+2) = Fin 2
```

The theorem keeps the `ctopMatrix u` unit-determinant hypothesis explicit.

## Source Fidelity

This is exactly the elementary p.13 coordinate readout: the regular variables
`B = C1 - I`, `F2`, and `F3` are encoded in `u` and are recovered as `u`; the
residual coordinates are the reduced passive-theta residual coordinates.

## Boundary

The theorem does not provide an inverse map from edge families to `(theta,u)`.
It does not prove original-prior transport, source-rank coverage, Haar
transport, a Jacobian formula, normal crossings, pole order, or RLCT
extraction.

## Verification

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_product_readout_axioms.lean
```

`./scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
The direct axiom probe for the new theorem reported only
`[propext, Classical.choice, Quot.sound]`.
