# Review - A2 p.13 Original-prior Volume-source-reference Finite Integral

Date: 2026-07-01.

Status: PASS after focused Lean checks and two xhigh read-only reviews.

## Scope/math reviewer

Reviewer: Banach the 2nd, xhigh explorer.

Verdict: PASS.

Checked:

- The new wrapper theorem keeps the old chart-piece, local-source,
  p.13-source-set, right-inverse, and density hypotheses, and replaces the old
  formal `muP13` inputs by exactly `AEMeasurable readback sourceRef`,
  `Measure.map readback sourceRef = coordinateSourceMeasure.restrict W`,
  `(originalEdgeFamilyVolume b).restrict chartPiece <= D • sourceRef`, and
  `D < infinity`.
- The proof derives the old formal readback assumptions with
  `Cformal := (cHaar : ENNReal) * D`, uses the source-reference bridge, and
  then applies the existing finite-integral theorem.
- The source-reference bridge treats restricted-volume domination and readback
  pushforward as assumptions, not claims.
- The reproduction and statement card match the Lean theorem and scalar.
- No overclaim was found: no source-reference identification, passive-theta
  source-image equality, source coverage, chart-image equality, Haar scalar
  normalization, normal crossings, pole order, or RLCT extraction.
- Imports remain Aoyagi-only in the reviewed files.

## Lean/API reviewer

Reviewer: Arendt the 2nd, xhigh explorer.

Verdict: PASS.

Checked:

- The existing `formalProductReadback` theorem was not semantically changed;
  the patch only inserts a new theorem after its proof.
- The new theorem first invokes the existing formal-product finite-integral
  theorem, then uses the source-reference bridge to build the formal readback
  assumptions.
- The `hfinite.2` handler order is correct: measurable, `U` subset,
  source-stratum subset, p.13 subset, readback/right-inverse, density bound,
  then formal readback assumptions.
- Scalar finiteness for `Cformal = (cHaar : ENNReal) * D` correctly uses
  `ENNReal.coe_lt_top` and `D < infinity`.
- No `sorry`, `axiom`, `native_decide`, or `#exit` appeared in the target file;
  `RLCT` appears only in nonclaim disclaimer comments.

## Local controller checks

- `lake env lean DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13ReadbackFiniteIntegral.lean` passed.
- `lake build DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyP13ReadbackFiniteIntegral` passed.
- `lake env lean DLNFibre.lean` passed.
- `lake build DLNFibre` passed.
- `./scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- `git diff --check` passed.
- Direct axiom probe for the new theorem reported only
  `[propext, Classical.choice, Quot.sound]`.
