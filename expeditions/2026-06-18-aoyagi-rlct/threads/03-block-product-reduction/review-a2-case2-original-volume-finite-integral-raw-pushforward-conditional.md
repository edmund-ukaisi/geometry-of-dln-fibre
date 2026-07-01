# Review - A2 Case 2 original-volume finite integral raw-pushforward conditional

Date: 2026-07-01.

Status: controller review PASS; Lean verification passed.

## Checks

- The raw-Haar raw-source pushforward remains an explicit chart-piece
  hypothesis.
- The finite-integral wrapper calls the original-volume readback front end,
  not the older bounded source-image wrapper with its independent `V`.
- The bridge is called with `G := W`, so the returned `V` is a same witness
  for the readback package and the raw-pushforward hypothesis.
- p.13 source-set containment and right-inverse hypotheses are derived from
  `chartPiece subset sourceChart '' V`, not supplied separately.
- The theorem is not described as original-volume transport or RLCT
  extraction.

## Boundary

This is the strongest current original-volume finite-integral statement in
the Case 2 passive-theta branch, but it is conditional.  The missing
mathematical theorem is still the local change-of-variables/Jacobian theorem
that would prove the raw-Haar raw-source pushforward or an equivalent
domination/density comparison.

## Verification

Focused elaboration, focused module build, full local `lake build DLNFibre`,
`lean/scripts/sorries`, `git diff --check`, and direct axiom probe passed.
The direct axiom probe reported only
`[propext, Classical.choice, Quot.sound]`.
