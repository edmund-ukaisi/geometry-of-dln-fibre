# Statement Card - A2 Retained-Passive Solved A1 Zero Frechet Derivative

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

## Lean Names

```text
fderiv_retainedPassive_A1TailAfterFirst_inv_eq_tail_fderiv
fderiv_retainedPassive_toCoordinateData_solvedA1_zero_apply
```

## Reproduction

```text
reproduction-a2-retained-passive-solved-a1-zero-fderiv.md
```

## Claim

At a retained-passive determinant-chart tuple, with

```text
Tfun(y) = retainedPassiveA1TailAfterFirst (ofTopologyTuple y).A1seed,
Tail    = Tfun(z),
dTail   = (fderiv Tfun z) v,
```

Lean proves

```text
d_z(solvedA1(0))(v)
  = Tail^-1 * v.Ctop
    - Tail^-1 * dTail * Tail^-1 * data.Ctop.
```

In tuple coordinates, `v.Ctop` is `v.2.2.2.2.1`.

## Method

The inverse-tail derivative is moved upstream into the derivative file and
stated over `TopologyTuple`, not over the downstream raw-order abbreviation.
The zero-branch theorem then applies the product rule to
`solvedA1(0) = Tail^-1 * Ctop`, uses the coordinate-projection derivative for
`Ctop`, and substitutes

```text
d(Tail^-1) = -(Tail^-1 * dTail * Tail^-1).
```

## Role

Together with the successor theorem
`fderiv_retainedPassive_toCoordinateData_solvedA1_succ_apply`, this completes
the local solved-`A1` derivative split needed before source-staging the
remaining `d(solvedA1 p)` terms in the retained-passive `dEarly` recurrence.

## Nonclaims

No recursive `dTail` formula, no finite-sum expansion, no full `dPcast`
source-staging, no target-side determinant theorem, no measure theorem, no
normal-crossing theorem, no pole-order theorem, and no RLCT theorem.
