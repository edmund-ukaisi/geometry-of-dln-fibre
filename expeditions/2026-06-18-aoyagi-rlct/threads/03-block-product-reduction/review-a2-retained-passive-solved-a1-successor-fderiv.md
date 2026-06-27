# Review - A2 Retained-Passive Solved A1 Successor Frechet Derivative

Date: 2026-06-27.

Reviewer: xhigh `Sagan`.

Verdict: PASS with statement adjustment.

## Findings

The successor solved-`A1` derivative formula is correctly scoped:

```text
d_z(solvedA1(p.succ))(v) = v.1 p.
```

The index `p.succ` is nonzero by `Fin.succ_ne_zero p`, so the solved-`A1`
definition takes the stored seed branch.  The stored seed branch is the
passive raw coordinate `A1passive p`, hence the derivative is the coordinate
projection.

No determinant-chart hypothesis is needed for this successor theorem.  The
chart hypothesis belongs to the zero branch because that branch differentiates
the inverse passive tail.

The theorem must be stated over the upstream `TopologyTuple ρ κ' R`, not the
downstream `RetainedPassiveRawTopologyTuple` abbreviation.  Otherwise
`RetainedPassiveCoordinatesDerivative.lean` would need to import
`RetainedPassiveFormalRawOrder.lean`, which is the wrong dependency direction
for this derivative foothold.

## Implemented Adjustment

The landed theorem uses:

```text
(z v : TopologyTuple ρ κ' R)
```

and the duplicate downstream theorem body was removed from
`RetainedPassiveCoordinatesJacobian.lean`.

## Nonclaims Checked

No determinant-chart membership, invertibility, formal raw-order Jacobian
identification, measure transport, normal-crossing theorem, pole order, or
RLCT consequence is claimed by this slice.
