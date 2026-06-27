# Review - A2 retained-passive dEarly terminal dPcast substitution

Date: 2026-06-27.

Reviewer: xhigh read-only scout `Volta`, integrated by controller.

Verdict: PASS.

## Scope Checked

The reviewed Lean target is

```text
fderiv_retainedPassiveLowerLeftProductTailSum_last_product_dCprod_dG_dPcast_apply
```

in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`.

It substitutes the solved-`A1` residual-product product rule into the explicit
terminal `dPcast` term of the already terminal `dCprod`/`dG` recurrence.

## Checks

- The theorem is the terminal counterpart of the nonterminal substitution:
  `q = Fin.last M`, `p = q.castSucc`, and `r = q.succ`.

- The solved-`A1` helper is instantiated with `M := M + 1` and
  `p := q.castSucc`.

- `Psucc` starts at `p.succ`.  The theorem does not use `r.succ` for the
  solved-`A1` successor product.

- The substituted term keeps the reviewed noncommutative order:

  ```text
  Cprod(z) * A3p(z) * Pcast(z)^-1
    * (dPsucc_z(v) * solvedA1_z(p)
        + Psucc(z) * d(solvedA1 p)_z(v))
    * Pcast(z)^-1.
  ```

- The theorem leaves the derivative of the current solved-`A1` factor
  explicit.  It does not replace it by a passive source tangent.

- The theorem deliberately does not collapse the terminal empty product
  `Psucc = 1` or its derivative.  Later xhigh review found that this cleanup
  is not available at these indices: `p.succ` is the penultimate endpoint, not
  the final endpoint.

## Lean Verification

The focused module build passed after implementation:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb \
  DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative
```

## Nonclaims

This theorem does not source-stage `d(solvedA1 p)`, does not collapse terminal
`Psucc`, does not distribute the substituted sum, and proves no target
staging, determinant equality, measure transport, normal crossings, pole
order, or RLCT statement.
