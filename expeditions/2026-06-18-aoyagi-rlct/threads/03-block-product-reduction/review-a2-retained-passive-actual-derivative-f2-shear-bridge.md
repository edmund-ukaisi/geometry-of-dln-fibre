# Review - A2 retained-passive actual derivative F2 shear bridge

Reviewer: xhigh read-only implementation reviewer `Anscombe the 5th`.

Status: PASS.

The reviewer found no blocking formalization or mathematical inaccuracies in
the F2 shear bridge.

Checks:

- The theorem uses `coord.F2 p.castSucc` for the current/source coefficient
  `F_p` and `coord.F2 p.succ` for the successor/full coefficient `H_p`.
- The endpoint convention is correct: `F2full` is the stored `F2` data with a
  terminal zero, so the terminal `p.succ` coefficient and derivative are zero.
- The correction term `-d(coord.F2 p.succ)(v) * coord.C p` is necessary and is
  present with the right matrix order.  It cancels the otherwise surviving
  successor-`F2` variation.
- The formal raw-order bridge matches
  `retainedPassiveFormalRawOrderJacobian_apply`: the F2 component is
  `-(coord.solvedA1 p + coord.F2 p.succ * coord.solvedA3 p) * z.2.1 p
  + coord.F2 p.succ * z.2.2.2.1 p`.
- The expedition notes do not overclaim a determinant factorization, measure
  pushforward, normal-crossing theorem, pole-order theorem, or RLCT theorem.

Non-blocking notes handled after review:

- The bridge docstring was tightened to mention both the top-left and
  successor-`F2` shear corrections, not just an upper-right target shear.
- The statement card now says that local `lake build` checks were used because
  the shared-cache `lean/scripts/lb` path was not writable in this sandbox.

The reviewer did not edit files and did not rerun Lean.
