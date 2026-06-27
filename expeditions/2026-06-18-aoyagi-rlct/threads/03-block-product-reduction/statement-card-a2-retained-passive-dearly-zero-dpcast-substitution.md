# Statement Card - A2 retained-passive dEarly zero dPcast substitution

Status: Lean proved; xhigh review passed.

## Claim

In the first-index specialization of the nonterminal retained-passive
`dEarly` recurrence, set

```text
q = 0 : Fin (M+1),
p = q.castSucc,
r = q.succ.
```

Substitute the zero-current solved-`A1` residual-product derivative into the
explicit `dPcast` term:

```text
dPcast_z(v)
  = dPsucc_z(v) * solvedA1_z(p)
    + Psucc(z) *
        (Tail^-1 * v.Ctop - Tail^-1 * dTail * Tail^-1 * data.Ctop).
```

The intended Lean statement preserves the full noncommutative order:

```text
Cprod(z) * A3p(z) * Pcast(z)^-1
  * (dPsucc_z(v) * solvedA1_z(p)
      + Psucc(z) *
          (Tail^-1 * v.Ctop - Tail^-1 * dTail * Tail^-1 * data.Ctop))
  * Pcast(z)^-1.
```

All `dCprod`, `dG`, and successor-tail terms remain exactly as in the already
staged recurrence.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

Planned Lean name:

```text
fderiv_retainedPassiveLowerLeftProductTailSum_zero_product_dCprod_dG_dPcast_apply
```

## Verification

Focused builds passed for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian`.  `scripts/sorries`
reported zero forbidden markers, `git diff --check` was clean, and the theorem
axiom audit reported only `[propext, Classical.choice, Quot.sound]`.

Review:

```text
review-a2-retained-passive-dearly-zero-dpcast-substitution.md
```

## Dependencies

- `fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dCprod_dG_dPcast_castSucc_apply`;
- `fderiv_retainedPassive_solvedA1_residualFactorProduct_castSucc_apply`;
- `fderiv_retainedPassive_solvedA1_residualFactorProduct_zero_castSucc_apply`.

## Cited

None.

## Deferred

Pointwise cleanup `solvedA1_z(0) = Tail^-1 * data.Ctop`; identification of
`Psucc` with the passive tail; recursive expansion of `dTail`; successor-index
`dEarly` source-staging; terminal cleanup; target staging; determinant theorem;
measure theorem; normal crossings; pole order; RLCT.

## Structure & Ideas Observed

The existing nonterminal `dEarly` theorem is indexed by `q : Fin M` and uses
the current factor `p = q.castSucc`.  To stage the zero solved-`A1` branch
without assuming `Fin M` is nonempty, the wrapper must instantiate that theorem
with `M := M+1` and then set `q = 0 : Fin (M+1)`.

## Kill Conditions

- The theorem must not quantify `q : Fin M := 0`.
- The theorem must preserve the factor order
  `Cprod * A3p * Pcast^-1 * (...) * Pcast^-1`.
- The theorem must keep `dPsucc`, `Psucc`, and `dTail` explicit.
- The theorem must not claim `Psucc = Tail` or expand `dTail`.
- The theorem must not claim determinant equality, measure transport, normal
  crossings, pole order, or RLCT.
