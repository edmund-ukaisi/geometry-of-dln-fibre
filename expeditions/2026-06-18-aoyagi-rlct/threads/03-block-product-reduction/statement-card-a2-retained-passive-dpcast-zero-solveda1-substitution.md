# Statement Card - A2 retained-passive dPcast zero solvedA1 substitution

Status: Lean proved; xhigh review passed.

## Claim

At a tuple determinant-chart point, specialize the solved-`A1` residual-product
derivative to the current factor `p = 0` and substitute the derivative of the
zero solved top-left block:

```text
dPcast_z(v)
  = dPsucc_z(v) * solvedA1_z(0)
    + Psucc(z) *
        (Tail^-1 * v.Ctop - Tail^-1 * dTail * Tail^-1 * data.Ctop).
```

Here `dTail` is the actual Frechet derivative of the passive top-left tail
map.  It is intentionally not expanded.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

Planned Lean name:

```text
fderiv_retainedPassive_solvedA1_residualFactorProduct_zero_castSucc_apply
```

## Verification

Focused builds passed for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian`.  `scripts/sorries`
reported zero forbidden markers, `git diff --check` was clean, and the theorem
axiom audit reported only `[propext, Classical.choice, Quot.sound]`.

Review:

```text
review-a2-retained-passive-dpcast-zero-solveda1-substitution.md
```

## Dependencies

- `fderiv_retainedPassive_solvedA1_residualFactorProduct_castSucc_apply`;
- `fderiv_retainedPassive_toCoordinateData_solvedA1_zero_apply`;
- the determinant-chart hypothesis for the zero solved-`A1` inverse-tail
  derivative.

## Cited

None.

## Deferred

Pointwise cleanup `solvedA1_z(0) = Tail^-1 * data.Ctop`; any identification
of `Psucc` with the passive tail; recursive expansion of `dTail`; downstream
`dEarly` specialization; target staging; determinant theorem; measure theorem;
normal crossings; pole order; RLCT.

## Structure & Ideas Observed

The product rule has already isolated the only new source-staging choice:
whether to substitute the current solved-factor derivative.  At `p = 0`, the
current solved factor is the inverse passive tail times `Ctop`, so its
derivative has the noncommutative inverse correction
`Tail^-1 * dTail * Tail^-1 * data.Ctop`.  The surrounding product contributes
this correction on the right of `Psucc(z)`.

## Route

Use the generic solved-`A1` residual-product product-rule theorem with
`p : Fin (M+1) := 0`.  Then use the zero solved-`A1` derivative theorem to
rewrite only

```text
(fderiv (fun y => A1fun y p) z) v.
```

Keep `dPsucc` explicit, and keep the first summand as
`dPsucc * data.toCoordinateData.solvedA1 p`.

## Kill Conditions

- The theorem must not commute matrix factors.
- The theorem must not replace `dPsucc` by `dTail`.
- The theorem must not expand `dTail`.
- The theorem must not touch downstream `dEarly` wrappers in this slice.
- The theorem must not claim determinant equality, measure transport, normal
  crossings, pole order, or RLCT.
