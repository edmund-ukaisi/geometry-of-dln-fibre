# Review - A2 retained-passive edge-pair product equivalence

Date: 2026-06-27.

Reviewer: Huygens, xhigh read-only implementation reviewer.

Verdict: PASS.

No blocking issues found.

## Checked

- Lean elaboration passed for
  `DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`.
- `edgeLocalFCPairPiLinearEquiv` preserves the edge-local product order and
  inverse formula.
- The raw `(F2,C)` regrouped equivalence preserves the separated-family order
  and the inverse signs.
- The point-specialized equivalence uses exactly
  `coord.solvedA1 p`, `coord.F2 p.succ`, and `coord.solvedA3 p`.
- The specialized inverse recovers only the source `(F2,C)` families from the
  formal raw-order output components.

## Nonclaims Checked

The Lean statements do not claim actual Frechet-derivative determinant
equality, do not include endpoint `Ctop` or `F3` factors, and do not infer
measure transport, normal crossings, pole order, or RLCT.

## Follow-up

The original statement card status said the Lean target was in progress; this
was stale and has been updated.
