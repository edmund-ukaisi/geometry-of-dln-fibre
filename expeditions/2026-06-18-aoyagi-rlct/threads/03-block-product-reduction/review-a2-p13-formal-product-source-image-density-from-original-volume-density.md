# Review: A2 p.13 formal-product source-image density from original-volume density

## Verdict

Pass, focused review.

## Checks

- The scalar is on the correct side: the formal-product measure is
  `cHaar` times original edge-family volume, so the formal-product density is
  `cHaar • volumeDensity`.
- The proof uses an equality route, not a domination route.
- No measurability hypothesis for `volumeDensity` is introduced, because
  `withDensity_smul'` only needs the scalar to be finite.
- The scalar finiteness condition is discharged by coercing the `NNReal`
  Haar scalar to `ENNReal`; `ENNReal.coe_ne_top` is enough.
- The statement keeps the original-volume density identity as a hypothesis.

## Verification

Verification passed:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13SourceMeasureBridge.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyP13SourceMeasureBridge
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_formal_density_from_volume_density_axioms.lean
```

The direct axiom probe reported only
`[propext, Classical.choice, Quot.sound]`.

## Remaining boundary

This theorem does not construct the source-image density identity, prove
source coverage, identify a passive-theta source image globally, normalize the
Haar scalar, prove normal crossings, prove a pole order, or extract an RLCT.
