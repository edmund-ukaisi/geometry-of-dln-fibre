# Review - A2 retained-passive dEarly zero dPcast substitution

Date: 2026-06-27.

Reviewer: xhigh `Pasteur`.

Status: PASS.

## Verdict

No blocking findings.

The Lean theorem

```text
fderiv_retainedPassiveLowerLeftProductTailSum_zero_product_dCprod_dG_dPcast_apply
```

correctly specializes the nonterminal retained-passive `dEarly` wrapper at
`M := M+1` and `q := 0 : Fin (M+1)`, then substitutes the zero-current
solved-`A1` residual-product derivative helper.

## Checks

- The theorem avoids the `Fin M` nonemptiness trap: the statement sets
  `q : Fin (M+1) := 0`, and the proof instantiates the generic nonterminal
  wrapper with `(M := M+1)` and that `q`.
- The factor order is faithful:

```text
Cprod * A3p * Pcast^-1 * (...) * Pcast^-1.
```

The bracket contains

```text
dPsucc * solvedA1 p
  + Psucc * (Tail^-1 * v.Ctop - Tail^-1 * dTail * Tail^-1 * data.Ctop).
```

No matrix factors are commuted.
- The zero-current substitution matches the prior zero solved-`A1`
  residual-product helper and the underlying zero solved-`A1` derivative.
- The statement-card formula matches the Lean statement after the controller
  repaired the missing middle `Tail^-1` in the prose formula.
- The nonclaims are appropriate: no `Psucc = Tail`, no recursive `dTail`
  expansion, no terminal cleanup, no target staging, no determinant or measure
  theorem, no normal crossings, no pole order, and no RLCT.

## Scope

Pasteur performed a read-only fidelity review and did not run Lean/build
commands.  The controller separately ran the focused builds, sorry scan,
whitespace check, and axiom audit.
