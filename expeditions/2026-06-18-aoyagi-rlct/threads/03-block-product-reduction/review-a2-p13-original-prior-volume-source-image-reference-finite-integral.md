# Review - A2 p.13 Original-prior Volume Source-image Reference Finite Integral

Date: 2026-07-01.

Status: PASS; local controller checks and xhigh final review passed.

## Route scout

Reviewer: Lovelace the 2nd, xhigh explorer.

Verdict: recommended the concrete source-image wrapper over stopping at the
`sourceRef := originalVolume.restrict chartPiece` specialization.

Key recommendation implemented: introduce a local passive-theta chart `V ⊆ W`,
set

```text
sourceRef := Measure.map sourceChart (coordinateSourceMeasure.restrict V),
Csource := 1,
```

use existing local inverse/source-image API to prove

```text
AEMeasurable readback sourceRef,
Measure.map readback sourceRef = coordinateSourceMeasure.restrict V,
```

then use `V ⊆ W` to dominate by `coordinateSourceMeasure.restrict W`.  The
original-volume domination by this concrete source-image reference remains an
explicit hypothesis.

## Final xhigh review

Reviewer: Ramanujan the 2nd, xhigh reviewer.

Verdict: PASS.  No blocking formalization or math-accuracy findings.

The source-image wrapper has the intended local shape: it returns `V ⊆ W` with
local inverse, injectivity, continuity, image measurability, and right-inverse
data; requires `chartPiece ⊆ sourceChart '' V`; and leaves

```text
originalVolume.restrict chartPiece ≤
  D • Measure.map sourceChart (coordinateSourceMeasure.restrict V)
```

as an explicit geometric measure hypothesis.  In the proof, the readback
pushforward of the concrete source reference is identified with
`coordinateSourceMeasure.restrict V`, then `V ⊆ W` gives domination by
`coordinateSourceMeasure.restrict W` with `Csource = 1`.

The smaller volume-readback wrapper is harmless: it specializes the parent
source-reference theorem with
`sourceRef := originalEdgeFamilyVolume.restrict chartPiece` and `D := 1`, while
still requiring readback measurability and source-measure domination as
hypotheses.

## Local controller checks

- `lake env lean DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13ReadbackFiniteIntegral.lean` passed.
- `lake build DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyP13ReadbackFiniteIntegral` passed.
- `lake env lean DLNFibre.lean` passed.
- Full local `lake build DLNFibre` passed.
- `lean/scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- `git diff --check` passed.
- Direct axiom probes for both new wrappers reported only
  `[propext, Classical.choice, Quot.sound]`.

## Nonclaims

This review target is still conditional.  It does not prove original-volume
domination by the source-image reference, identify a global passive-theta
image, prove source coverage, chart-image equality, source-rank coverage, Haar
scalar normalization, normal crossings, pole order, RLCT extraction, or global
original-prior integrability beyond the supplied local chart piece.
