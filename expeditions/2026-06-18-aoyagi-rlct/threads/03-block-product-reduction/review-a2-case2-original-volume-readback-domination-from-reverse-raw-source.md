# Review: A2 Case 2 original-volume readback domination from reverse raw-source domination

Status: PASS.

## Controller check

The theorem is a conditional handoff, not a new analytic transport theorem.
Its proof first obtains a source-chart shrink with readback, injectivity,
continuity, measurable image, and p.13 source-set containment.  It then runs
the reverse raw-source original-volume bridge inside that shrink and inherits
the source-chart properties to the smaller bridge shrink.

The scalar direction is correct:

```text
rawHaar|rawSource <= D * rawMap_*(thetaReference|V)
```

feeds the existing bridge as

```text
originalVolume|C <= (cHaar^{-1} * D) * sourceRef(V).
```

Mapping through `readback` uses the exact local identity

```text
readback_* sourceRef(V) = thetaReference|V <= thetaReference|G.
```

The theorem keeps `chartPiece` measurable and inside the actual image
`sourceChart '' V`; p.13 source-set containment is derived from this image
containment.

## Boundary

No claim is made that Aoyagi pp.10-13 prove the reverse raw-source domination.
The missing substantial theorem remains a local change-of-variables,
coverage, or bounded-below density comparison for the source image.

## Verification

Focused warning-clean elaboration passed:

```text
env LEAN_NUM_THREADS=3 lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadback.lean
```

Full build, sorry audit, diff check, axiom audit, and xhigh reviewer result
all passed.

Verification commands:

```text
env LEAN_NUM_THREADS=3 lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadback.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalVolumeReadback
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_reverse_raw_source_readback_axioms.lean
```

The direct axiom probe reports only
`[propext, Classical.choice, Quot.sound]`.

Xhigh read-only reviewer `Newton` passed the theorem shape and scalar
direction.  The only note was non-blocking Lean fragility: the proof uses
`simpa` through the concrete `Case2PassiveTheta` field representation when
restricting source-chart properties from `V0` to `V`.  This is not unsound,
but a future adapter lemma could make the proof less representation-sensitive.
