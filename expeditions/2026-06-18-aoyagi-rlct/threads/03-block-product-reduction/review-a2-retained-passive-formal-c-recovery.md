# Review - A2 retained-passive formal C recovery

Reviewer: xhigh read-only reviewer `Huygens the 5th`.

Status: PASS.

Controller note: this is the companion to the formal `F2` recovery.  The
intended proof recovers `v.F2_p`, then uses the formal `C` formula
`u.C_p = -G * v.F2_p + v.C_p` to cancel the lower-left shear.

The reviewer found no blocking issue.  The algebra and matrix order match the
formal raw-order map:

```text
F2_p = -(A + F*G)*x + F*y,
C_p  = -G*x + y.
```

The Lean theorem statement matches the target-coordinate recovery formula.
The proof correctly depends on
`retainedPassiveFormalRawOrderJacobianAt_recovers_F2` rather than duplicating
the determinant-chart argument, then unfolds the formal `C` component and
cancels `-G*x + y + G*x`.

The `C` recovery introduces no new invertibility beyond the previous `F2`
recovery's use of solved-`A1` invertibility on the retained-passive determinant
chart.  No determinant equality, actual derivative identification, measure
transport, normal crossings, pole order, or RLCT is claimed.
