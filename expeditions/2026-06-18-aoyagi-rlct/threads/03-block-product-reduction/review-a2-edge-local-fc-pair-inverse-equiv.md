# Review - A2 edge-local `(F,C)` pair inverse equivalence

Reviewer: xhigh read-only reviewer `Halley the 5th`.

Status: PASS.

Controller note: this generic inverse/equivalence is intended to be the
reusable form of the retained-passive formal `F2`/`C` recovery identities.
It must stay finite-linear and must not claim the retained-passive total
target-side shear or actual derivative determinant comparison.

The reviewer initially returned FAIL because the first implementation used a
heartbeat-heavy proof that did not elaborate under normal build defaults.  The
controller replaced it with explicit matrix identities and reran the focused
build successfully.  On re-review, `Halley the 5th` returned PASS:

- the normal focused determinant-helper build elaborates;
- the inverse apply formula is
  `(U,V) |-> (A^{-1} * (H*V - U), V + G*(A^{-1} * (H*V - U)))`;
- the proof uses the identities
  `A * (A^{-1} * (H*V - U)) = H*V - U` and
  `H*(-G*F + C) - (-(A + H*G)*F + H*C) = A*F`;
- the noncommutative order is correct throughout;
- the nonclaim boundary remains finite-linear only.
