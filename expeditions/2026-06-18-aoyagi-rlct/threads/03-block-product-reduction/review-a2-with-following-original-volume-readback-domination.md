# Review - A2 with-following original-volume readback domination

Date: 2026-07-02.

Reviewer: Codex xhigh independent reviewer.

## Verdict

PASS.

I found no blocking formalisation-soundness, claim-precision, source-fidelity,
or overclaiming issue in the reviewed theorem, reproduction note, or statement
card.

## Reviewed Target

Lean theorem:

```text
DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource
```

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadback.lean
```

Companion notes:

```text
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/reproduction-a2-with-following-original-volume-readback-domination.md
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/statement-card-a2-with-following-original-volume-readback-domination.md
```

## Findings

No blocking findings.

Non-blocking prose precision note: the reproduction note says that the smaller
set `V` inherits "measurable-image data by restriction." In Lean, this is not
using measurability of a subset of `sourceChart '' V0`; it re-establishes
`MeasurableSet (sourceChart '' V)` from openness of `V`, `ContinuousOn
sourceChart V`, and `Set.InjOn sourceChart V`. The proof is correct. Future
prose would be slightly sharper if it said the image-measurability claim is
re-established on the smaller open set.

## Soundness Checks

The formal statement keeps the expected local hypotheses explicit:

- `MeasurableSet chartPiece`;
- `chartPiece subset sourceChart '' V`;
- `chartPiece subset p13SourceSet`;
- `Measure.map rawMap (thetaReference.restrict V) = rawHaar.restrict rawSourceSet`.

The proof uses the expected components:

- the with-following source-chart package for left inverse, injectivity,
  continuity, and local image measurability;
- the with-following original-volume/source-reference domination theorem;
- the generic readback measure handoff, plus the standard local readback
  pullback lemmas for `Measure.map sourceChart (thetaReference.restrict V)`.

The raw-pushforward equality is passed as an assumption to the upstream
original-volume domination theorem. The proof does not construct raw Haar
transport. The p.13 containment of `chartPiece` is also passed as an assumption;
the proof does not derive p.13 image coverage.

## Source Fidelity

The reviewed claim is an Aoyagi-local formal packaging result. The theorem and
notes do not cite or rely on non-Aoyagi mathematical sources, and they do not
state an RLCT, normal-crossing, pole-order, or prior-transport conclusion.

## Verification

Ran from the requested worktree:

```text
git status --short --branch
```

This confirmed branch `expedition/aoyagi-rlct` and showed pre-existing dirty
files. I did not modify code or ledgers.

Ran focused elaboration from `lean/`:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadback.lean
```

Result: passed.

Ran textual audits with `rg` for the target theorem, required hypotheses,
overclaim boundary terms, and placeholder terms. The placeholder audit found no
`sorry`, `admit`, `axiom`, or `unsafe` occurrence in the reviewed Lean file;
the only hit in the reviewed artifacts was the statement card's own
"no-sorry audit" status line.

Did not run a full `lake build DLNFibre`. Did not use `scripts/lb`.

## Nonclaim Boundary

This review reads the theorem as proving only:

- existence of the final local open `V`;
- source-chart left inverse, injectivity, continuity, and measurable image on
  that `V`;
- readback a.e. measurability for `originalVolume.restrict chartPiece`;
- domination of the readback pushforward by the stated inverse-Haar scalar times
  `thetaReference.restrict G`.

It does not prove or claim:

- raw-Haar transport;
- determinant-Haar transport;
- p.13 source-image coverage;
- source-prior or original-prior transport;
- density lower-bound removal;
- normal crossings;
- pole order;
- RLCT extraction.
