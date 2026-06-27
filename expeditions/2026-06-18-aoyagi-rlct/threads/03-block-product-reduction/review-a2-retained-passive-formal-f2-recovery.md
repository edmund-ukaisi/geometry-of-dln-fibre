# Review - A2 retained-passive formal F2 recovery

Reviewers: xhigh read-only explorers `Ampere the 5th` and `Kepler the 5th`.

Status: PASS.

Controller note: the focused Lean build for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passes.  The theorem
is intentionally scoped to formal target-coordinate recovery and does not claim
a determinant theorem.

Both reviewers found no blocking issue.  The recovery proof correctly
simplifies

```text
F * u.C - u.F2
```

to

```text
A * v.F2
```

using the formal raw-order `(F,C)` formulas, then applies inverse cancellation
from the determinant-chart invertibility theorem
`solvedA1_det_isUnit_of_detChart`.

The chart input is appropriate: `detChart` supplies invertibility for every
`coord.solvedA1 p`, including `p = 0`.  The theorem is scoped honestly as a
formal-map recovery identity, not as an actual Frechet derivative statement and
not as a determinant theorem.

Suggested next determinant-relevant target from `Kepler the 5th`:

```text
retainedPassiveFormalRawOrderJacobianAt_recovers_C
```

recovering `v.C_p` from the same formal target pair after substituting the
recovered `F2`.
