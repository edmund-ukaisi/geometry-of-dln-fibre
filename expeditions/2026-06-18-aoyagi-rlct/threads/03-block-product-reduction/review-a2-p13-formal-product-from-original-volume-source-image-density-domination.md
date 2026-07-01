# Review: A2 p.13 formal-product domination from original-volume source-image density

## Verdict

Pass, focused review.

## Checks

- The scalar direction is correct: the formal-product chart measure is
  `cHaar` times the original-volume chart-piece measure, so the source
  domination scalar is `(cHaar : ENNReal) * D`.
- No inverse scalar is introduced in this forward direction.
- The proof is measure bookkeeping only: it first derives
  `originalEdgeFamilyVolume.restrict chartPiece <= D • sourceRef` from the
  supplied `withDensity` identity and a.e. bound, then invokes the existing
  formal-product/original-volume domination transfer.
- The theorem keeps the original-volume source-image density identity and
  density bound as explicit hypotheses.

## Verification

Verification passed:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13SourceMeasureBridge.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyP13SourceMeasureBridge
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_formal_from_volume_source_image_axioms.lean
```

The direct axiom probe reported only
`[propext, Classical.choice, Quot.sound]`.

## Remaining boundary

This theorem does not construct the source-image density identity, prove
source coverage, identify a passive-theta source image globally, normalize the
Haar scalar, prove normal crossings, prove a pole order, or extract an RLCT.
