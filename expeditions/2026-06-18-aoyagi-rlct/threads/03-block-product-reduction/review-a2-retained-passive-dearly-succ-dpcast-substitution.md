# Review - A2 retained-passive dEarly successor dPcast substitution

Date: 2026-06-27.

Reviewer: xhigh `Kierkegaard`.

Status: PASS.

## Verdict

No blocking mathematical or indexing-fidelity findings.

The Lean theorem

```text
fderiv_retainedPassiveLowerLeftProductTailSum_succ_product_dCprod_dG_dPcast_apply
```

correctly specializes the non-first retained-passive `dEarly` wrapper and
substitutes the successor-current solved-`A1` residual-product derivative.

## Checks

- The theorem sets

```text
q = s.succ,
u = s.castSucc,
p = q.castSucc,
r = q.succ.
```

- The proof uses the generic nonterminal recurrence with `(M := M+1)` and
  `q := s.succ`.
- The successor `dPcast` helper is instantiated with `u`, not `q`; the bridge
  `u.succ = p` is proved by `Fin.succ_castSucc`.
- The tangent term is `v.1 u`, hence `v.1 s.castSucc`; it is not `v.1 s`,
  `v.1 q`, or `v.1 s.succ`.
- The factor order is preserved:

```text
Cprod * A3p * Pcast^-1 * (...) * Pcast^-1.
```

- The reproduction and statement card match the Lean indices, helper index,
  tangent, factor order, and nonclaims.

## Scope

Kierkegaard performed a read-only fidelity review and did not run Lean/build
commands.  The controller separately ran the focused builds, sorry scan,
whitespace check, and axiom audit.
