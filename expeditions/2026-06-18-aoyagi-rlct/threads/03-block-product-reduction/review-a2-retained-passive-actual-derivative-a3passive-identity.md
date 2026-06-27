# Review - A2 Retained-Passive Actual Derivative Passive A3 Identity

Date: 2026-06-27.

Status: reviewed; no blocker.

Reviewer: xhigh read-only explorer `Mendel the 5th`.

## Verdict

Pass.

## Checked Points

The reviewer confirmed that, for `p : Fin M`, the raw-order target lower-left
passive component reduces globally to the input projection:

```text
(topologyTupleEdgeRawOrder y).A3passive p = y.A3passive p.
```

The checked reduction chain is:

```text
topologyTupleEdgeRawOrder_A3passive
  -> solvedA3 p.castSucc
  -> A3seed p.castSucc        since p.castSucc != Fin.last M
  -> A3passive p.
```

The determinant-chart hypothesis is only used to invoke the existing
differentiability theorem for the full raw-order map and identify the actual
Frechet derivative.

The reviewer also confirmed the optional formal bridge: the apply formula for
`retainedPassiveFormalRawOrderJacobianAt` leaves the raw lower-left passive
tangent slot as `v.2.2.1`, so the analytic passive readout agrees
coordinatewise with the point-specialized formal raw-order map.

## Caveats

- The result is only for passive `p : Fin M`, equivalently the raw edge
  `p.castSucc`.
- It does not cover the terminal `Fin.last M` lower-left endpoint, where the
  final solve is nontrivial.
- It proves one coordinate of the analytic derivative, not full equality with
  `retainedPassiveFormalRawOrderJacobianAt`, determinant equality, or any
  measure/Jacobian-density theorem.
