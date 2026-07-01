# Review - A2 p.13 formal-product source-image readback domination

## Verdict

PASS for the stated socket.

## Scope check

The theorem assumes the bounded-density identity

```text
muP13 = (sourceRef.withDensity delta).restrict chartPiece
```

and the a.e. bound `delta <= D`.  It does not manufacture either fact.  The
conclusion is only readback a.e.-measurability and

```text
Measure.map readback muP13 <= D * coordinateSourceMeasure.restrict W.
```

This matches the intended next socket for the formal-product/source-image
frontier.

## Scalar check

The scalar is the supplied source-image density bound `D`.  No inverse Haar
factor appears, because the theorem does not pass through original edge-family
volume.  This agrees with the pen-and-paper calculation.  Downstream prior
statements may still introduce `cHaar^{-1}` through the existing original-volume
or original-prior bridges.

## Direction check

The inequality direction is from the restricted p.13 formal-product measure to
the coordinate source measure after readback.  The proof is the generic
source-image bounded-density pullback, followed by restriction monotonicity
from `V` to `W`.  This is the direction needed by the existing
formal-product-readback finite-integral socket.

## Risk boundary

The unresolved mathematical frontier remains the actual comparison between the
p.13 formal-product chart measure and the passive-theta source-image reference.
The xhigh scouts independently identified that comparison, not this readback
bookkeeping, as the real gap.  In particular, boundedness of
`sourceImageDensity` alone does not imply domination if the source-image
reference vanishes on formal-product mass.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13ReadbackFiniteIntegral.lean`
- `lake build DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyP13ReadbackFiniteIntegral`
- `lake build DLNFibre`
- `lean/scripts/sorries`
- `git diff --check`
- direct `#print axioms` probe for the new theorem

All checks passed locally.  The full build emitted existing imported-module
linter warnings.  The direct axiom probe reported only
`[propext, Classical.choice, Quot.sound]`.

A separate xhigh post-implementation reviewer was blocked by the recovered VM
shell launcher before it could inspect files; that blocked review is not counted
as positive evidence.
