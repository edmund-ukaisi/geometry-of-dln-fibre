# Review - A2 retained-passive F3 positive-tail dLast target staging

Date: 2026-06-27.

Reviewer: xhigh `Raman`.

Verdict: PASS.

## Scope

Reviewed the new Lean theorems in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

with the reproduction and statement card:

```text
reproduction-a2-retained-passive-f3-positive-tail-dlast-target-staged.md
statement-card-a2-retained-passive-f3-positive-tail-dlast-target-staged.md
```

## Findings

No blocking issue.

The Lean statements use a terminal passive index `q : Fin M` with
`q.succ = Fin.last M`.  The noncommutative `F3` bridge order is preserved:
only the terminal `dLast` factor is replaced inside

```text
(coord.F3 - Earlyfun z) * ...
```

and the early-tail derivative remains explicit as

```text
(fderiv Earlyfun z) v.
```

The terminal raw lower-left target readout is not declared zero.  It remains
visible under the explicit multiplier

```text
coord.F2 q.succ.succ * rawEdgeTupleA3(Dzv,q.succ).
```

The theorem names accurately advertise `dLast` staging only.  The reproduction
and statement card state the nonclaims: no full positive-tail `F3` target
staging, no `dEarly` recurrence, no determinant-one target-side shear,
determinant equality, measure transport, normal crossings, pole order, or
RLCT.

## Cleanup applied

The reproduction and statement card status lines were updated after the Lean
target landed and the focused/full builds plus sorry, whitespace, and axiom
audits passed.
