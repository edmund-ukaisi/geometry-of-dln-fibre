# Review - A2 retained-passive dEarly dPcast substitution

Date: 2026-06-27.

Reviewer: xhigh read-only scout `Euclid`, integrated by controller.

Verdict: PASS.

## Scope Checked

The reviewed Lean target is

```text
fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dCprod_dG_dPcast_castSucc_apply
```

in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`.

It substitutes the already-proved solved-`A1` residual-product product rule
into the explicit `dPcast` factor of the retained-passive `dEarly` recurrence,
after the `dCprod` and `dG` factors have already been staged.

## Checks

- The theorem uses the correct nonterminal indices:

  ```text
  p = q.castSucc : Fin (M+1),
  r = q.succ     : Fin (M+1).
  ```

- The solved-`A1` product helper is instantiated at `p`, so
  `Pcast` starts at `p.castSucc` and `Psucc` starts at `p.succ`.
  It does not use `r.succ`, which would advance one factor too far.

- The substituted term has the reviewed noncommutative order:

  ```text
  Cprod(z) * A3p(z) * Pcast(z)^-1
    * (dPsucc_z(v) * solvedA1_z(p)
        + Psucc(z) * d(solvedA1 p)_z(v))
    * Pcast(z)^-1.
  ```

- The rightmost `(Pcast z)^-1` remains outside the substituted sum.

- The derivative of the current solved-`A1` factor remains explicit as
  `(fderiv solvedA1(p))_z(v)`.  The theorem does not identify it with a
  passive source tangent, which would be false at `p = 0`.

## Lean Verification

The focused module build passed after the review:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb \
  DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative
```

## Nonclaims

This theorem does not source-stage `(fderiv solvedA1(p))_z(v)`, does not
iterate the successor `dPsucc` term, does not collapse the successor tail or
`Cnext` derivative, does not distribute the matrix sum through surrounding
factors, and proves no determinant equality, measure transport, normal
crossings, pole order, or RLCT statement.
