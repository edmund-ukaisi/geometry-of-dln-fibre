# Review - A2 retained-passive target edge-pair linear map

Date: 2026-06-28.

Reviewer: xhigh `Lovelace the 2nd`.

Verdict: PASS.

## Scope

Reviewed the uncommitted target edge-pair linear-map layer in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`, plus:

```text
reproduction-a2-retained-passive-target-edge-pair-linear-map.md
statement-card-a2-retained-passive-target-edge-pair-linear-map.md
```

## Findings

- `retainedPassiveTargetRecoveredF2LinearMapAt` faithfully packages
  `retainedPassiveTargetRecoveredF2At`.  The terminal formula matches the
  existing terminal recurrence, and the nonterminal formula preserves the
  `Xsucc * coord.C q` subtraction and the same
  `LinearEquiv.cast ... (Fin.succ_castSucc p).symm` cast.
- `retainedPassiveTargetRecoveredSuccessorF2LinearMapAt` faithfully packages
  `retainedPassiveTargetRecoveredSuccessorF2At`, including the nonterminal cast
  branch and terminal zero branch.
- `retainedPassiveTargetEdgePairShearLinearMapAt` faithfully packages
  `retainedPassiveTargetEdgePairShearAt`; it builds only the separated
  `(F2,C)` target-side component map by `Fmap.prod Cmap`.
- The notes and statement card keep the claim local: no target-side
  `LinearEquiv`, whole raw-tuple normalizer, determinant-one theorem,
  determinant equality, source-prior transport, normal crossings, pole order,
  RLCT, or analytic extraction is claimed.

## Follow-Up Addressed

The initial review noted that the statement-card status was stale and that the
generic matrix-multiplication/projection helper names were public.  The card is
now marked reviewed, and implementation helpers in the Lean block are private;
the public API remains the intended linear-map package.
