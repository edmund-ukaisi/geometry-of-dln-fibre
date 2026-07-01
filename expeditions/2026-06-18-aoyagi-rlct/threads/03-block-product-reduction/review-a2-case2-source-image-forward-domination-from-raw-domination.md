# Review - A2 Case 2 source-image forward domination from raw domination

Date: 2026-07-01.

Status: post-Lean controller review PASS for statement direction, boundary,
and verification.

## Checks

- The hypothesis must be domination, not equality:
  `Measure.map rawMap (...) <= C * rawHaar.restrict rawSourceSet`.
- The conclusion must be the forward comparison:
  `Measure.map sourceChart (...) <= (C * cHaar) * originalVolume.restrict p13SourceSet`.
- The theorem name must include `le_smul_originalEdgeFamilyVolume`, not
  `eq` and not `readback`.
- The documentation must state that this is the wrong direction for the
  original-volume readback finite-integral socket.
- No claim may be made that Aoyagi p.13 proves raw-Haar/source-prior transport.

## Verdict

The statement is an honest consequence of existing p.13 measure bridges and
is useful as a boundary marker.  It does not close the main raw-pushforward
gap.  A future theorem removing the current equality hypothesis still needs a
reverse domination, equality, or local density lower-bound/change-of-variables
result.

## Verification

Focused elaboration, focused module build, full local `lake build DLNFibre`,
`lean/scripts/sorries`, `git diff --check`, and direct theorem axiom audits
passed.  Both new declarations report only
`[propext, Classical.choice, Quot.sound]`.
