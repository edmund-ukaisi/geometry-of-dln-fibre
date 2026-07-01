# Review - A2 Case 2 original-volume/source-image domination from formal-product domination

Date: 2026-07-01.

Status: post-Lean controller review PASS for statement direction, boundary,
and verification.

## Checks

- The conclusion is the needed direction:
  `originalVolume.restrict chartPiece <= constant • sourceRef`.
- The hypothesis is not raw-Haar equality and not forward raw domination.  It
  is the still-missing formal-product/source-image domination:
  `muP13.restrict chartPiece <= D • sourceRef`.
- The theorem must derive p.13 source-set containment only from
  `chartPiece subset sourceChart '' V` and the already-proved image support.
- The theorem must not claim that Aoyagi p.13 proves the supplied domination.

## Verdict

The statement is a sound and useful bridge.  It turns the next genuine
change-of-variables target into exactly the original-volume domination needed
by existing finite-integral/readback consumers.  The mathematical gap remains
the formal-product/source-image comparison itself.

## Verification

Focused warning-clean elaboration, focused module build, dependent readback
module build, full local `lake build DLNFibre`, `lean/scripts/sorries`,
`git diff --check`, and direct theorem axiom audit passed.  The theorem
reports only `[propext, Classical.choice, Quot.sound]`.
