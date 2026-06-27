# Statement Card - A2 retained-passive dEarly successor dPcast substitution

Status: Lean proved; xhigh review passed.

## Claim

For `s : Fin M`, specialize the nonterminal retained-passive `dEarly`
recurrence at

```text
q = s.succ     : Fin (M+1),
u = s.castSucc : Fin (M+1),
p = q.castSucc : Fin ((M+1)+1),
r = q.succ     : Fin ((M+1)+1).
```

Since `u.succ = p`, the current solved-`A1` factor is a successor factor.
Substitute the successor-current solved-`A1` residual-product derivative into
the explicit `dPcast` term:

```text
dPcast_z(v)
  = dPsucc_z(v) * solvedA1_z(p)
    + Psucc(z) * v.1 u.
```

The intended Lean statement preserves the full noncommutative order:

```text
Cprod(z) * A3p(z) * Pcast(z)^-1
  * (dPsucc_z(v) * solvedA1_z(p)
      + Psucc(z) * v.1 s.castSucc)
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
fderiv_retainedPassiveLowerLeftProductTailSum_succ_product_dCprod_dG_dPcast_apply
```

## Verification

Focused builds passed for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian`.  `scripts/sorries`
reported zero forbidden markers, `git diff --check` was clean, and the theorem
axiom audit reported only `[propext, Classical.choice, Quot.sound]`.

Review:

```text
review-a2-retained-passive-dearly-succ-dpcast-substitution.md
```

## Dependencies

- `fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dCprod_dG_dPcast_castSucc_apply`;
- `fderiv_retainedPassive_solvedA1_residualFactorProduct_castSucc_apply`;
- `fderiv_retainedPassive_solvedA1_residualFactorProduct_succ_castSucc_apply`;
- `Fin.succ_castSucc` for the equality `s.castSucc.succ = s.succ.castSucc`.

## Cited

None.

## Deferred

Terminal cleanup; expansion of `dPsucc`; pointwise cleanup of suffix products;
target staging; determinant theorem; measure theorem; normal crossings; pole
order; RLCT.

## Structure & Ideas Observed

The existing nonterminal `dEarly` theorem uses the current factor
`p = q.castSucc`.  To avoid the first factor and use the successor solved-`A1`
branch, set `q = s.succ`; then `p = q.castSucc = (s.castSucc).succ`.
Therefore the successor helper applies with helper index `s.castSucc`, and the
tangent is `v.1 s.castSucc`.

## Kill Conditions

- The theorem must not use tangent `v.1 s`, `v.1 q`, or `v.1 s.succ`.
- The theorem must instantiate the successor `dPcast` helper with
  `s.castSucc`.
- The theorem must preserve the factor order
  `Cprod * A3p * Pcast^-1 * (...) * Pcast^-1`.
- The theorem must not introduce `dTail`, terminal cleanup, determinant
  equality, measure transport, normal crossings, pole order, or RLCT.
