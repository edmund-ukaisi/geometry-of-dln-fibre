# Review - A2 Retained-Passive Formal Non-Edge Recovery

Date: 2026-06-27.

Reviewer: Nash, xhigh read-only explorer.

## Verdict

PASS.

## Boundary Check

The implemented Lean statements match the intended formal recovery slice:

- `A1passive` is projection recovery, indexed by `p : Fin M`, and needs no
  chart hypothesis.
- `Ctop` proves `Tail * u.Ctop = v.Ctop`, using left cancellation
  `Tail * (Tail⁻¹ * C) = C` and determinant-unitness of `Tail`.
- `F3` proves `u.F3 * (-(coord.solvedA1 (Fin.last M)))⁻¹ = v.F3`, using right
  cancellation after the formal output is `v.F3 * (-LastTop)`.

## Endpoint And Unit Risks

- `A1passive` is indexed by `Fin M`, not `Fin (M+1)`.
- `LastTop` is `coord.solvedA1 (Fin.last M)` with
  `Fin.last M : Fin (M+1)`, not an `F3` endpoint index.
- `F3` has shape `Matrix (κ' (Fin.last (M+1))) ρ ℝ`; the `-LastTop` factor
  acts on the right.
- `Ctop` uses `Matrix.mul_nonsing_inv_cancel_left`; `F3` uses
  `Matrix.mul_nonsing_inv_cancel_right`.
- The determinant-chart hypothesis is necessary for `Ctop` and `F3`.

## False Statements To Avoid

- The recovery lemmas do not identify the actual Frechet derivative with the
  formal map.
- They do not source-stage `Ctop` or `F3`.
- They do not prove a target-side determinant-one equivalence, determinant
  equality for the actual derivative, density/measure transport, normal
  crossings, pole order, or RLCT.

## Naming Notes

The theorem names are appropriate:

```text
retainedPassiveFormalRawOrderJacobianAt_recovers_A1passive
retainedPassiveFormalRawOrderJacobianAt_recovers_Ctop
retainedPassiveFormalRawOrderJacobianAt_recovers_F3
```

They belong in `RetainedPassiveCoordinatesJacobian.lean` because they are
point-specialized recovery facts depending on `ofTopologyTuple` and chart data.
