# Statement Card - A2 Retained-Passive Tail-Inverse Frechet Derivative

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

## Lean Names

```text
fderiv_retainedPassive_A1TailAfterFirst_inv_eq_tail_fderiv
Ctop_tail_fderiv_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
```

## Reproduction

```text
reproduction-a2-retained-passive-tail-inverse-fderiv.md
```

## Claim

At a retained-passive determinant-chart point, if

```text
Tfun(y) = retainedPassiveA1TailAfterFirst (ofTopologyTuple y).A1seed,
Tail    = Tfun(z),
dTail   = (fderiv Tfun z) v,
```

then

```text
(fderiv (fun y => Tfun(y)^{-1}) z) v
  = - Tail^{-1} * dTail * Tail^{-1}.
```

Combining this with the previous Ctop successor-staging theorem gives the
strengthened Ctop formula

```text
Dzv.Ctop
  - X_F(0) * coord.solvedA3_0
  - coord.F2_1 * X_G(0)
  + Tail^{-1} * dTail * Tail^{-1} * coord.Ctop
= formal(z)(v).Ctop.
```

## Proof Plan

1. Use determinant-chart membership and
   `retainedPassiveA1TailAfterFirst_det_isUnit_of_passive` to prove
   `IsUnit Tail.det`.
2. Use the existing differentiability theorem for the tail map.
3. Apply `hasFDerivAt_matrix_inv_of_isUnit_det` and compose with the tail map.
4. Rewrite the previous Ctop successor-staged bridge with the inverse-tail
   derivative formula.

## Status

Lean implementation landed locally.  Focused
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` build passed, and the
full `DLNFibre` build passed.  Independent xhigh implementation review passed
in `review-a2-retained-passive-tail-inverse-fderiv.md`.  `scripts/sorries`
reported zero forbidden markers, `git diff --check` passed, and both new
theorem axiom audits report only `[propext, Classical.choice, Quot.sound]`.

## Nonclaims

This does not compute `dTail` as a recursive product and does not make the
`Ctop` branch fully source-staged.  It is not a target-side `LinearEquiv`,
determinant-one shear, determinant equality, measure theorem, normal-crossing
theorem, pole-order theorem, or RLCT theorem.
