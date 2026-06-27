# Statement Card - A2 retained-passive terminal `F2` target shear

Status: reproduced, Lean-proved, and xhigh-reviewed.

## Claim

At the terminal retained-passive edge `p = Fin.last M`, the existing actual
`F2` derivative bridge loses its successor-`F2` derivative term because the
successor slot is the terminal zero convention.  Thus

```text
dY12_p + dA1_p * coord.F2 p.castSucc
= formal.F2_p.
```

## Lean Target

Expected Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Expected Lean names:

```text
fderiv_retainedPassive_toCoordinateData_F2_last_apply
F2_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
```

## Dependencies

- `F2full_last` and `toCoordinateData`;
- `fderiv_const_apply`;
- `F2_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`.

## Kill Conditions

- If the theorem is stated for all edges, it overclaims.  Nonterminal edges
  still carry a successor derivative term.
- If the terminal successor slot is not definitionally
  `Fin.last (M+1)`, the zero-derivative proof must be adjusted rather than
  assumed.

## Nonclaims

No nonterminal target-side shear, no full determinant factorization, no
measure theorem, no normal crossings, no pole order, and no RLCT follows from
this terminal-edge bridge alone.
