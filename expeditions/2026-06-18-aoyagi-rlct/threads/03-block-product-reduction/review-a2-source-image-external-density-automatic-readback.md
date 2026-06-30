# Review - A2 source-image external density automatic readback

Date: 2026-06-30.

## Verdict

PASS after focused and full Lean verification.

## Soundness Check

The theorem is a wrapper around two already established facts:

1. continuous injective local chart plus left inverse gives readback
   a.e. measurability for the chart-produced source-image reference;
2. bounded-density identification of a restricted external measure gives
   scalar domination after pullback by readback.

The external measure is not arbitrary.  The statement requires the exact
restricted-measure equality with a `withDensity` perturbation and the a.e.
upper bound on that density.

## Source Fidelity

The statement is compatible with Aoyagi p.13 because its coordinate domain is
generic.  It can later be instantiated with full product coordinates, including
regular variables, once the actual p.13 source chart/readback and source-prior
density identity are available.

## Boundary

This is not original-prior transport.  It does not prove source-image coverage,
Haar transport, a Jacobian formula, normal crossings, pole order, or RLCT
extraction.

## Verification

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_external_density_axioms.lean
```

`./scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
The direct axiom probe for the new theorem reported only
`[propext, Classical.choice, Quot.sound]`.
