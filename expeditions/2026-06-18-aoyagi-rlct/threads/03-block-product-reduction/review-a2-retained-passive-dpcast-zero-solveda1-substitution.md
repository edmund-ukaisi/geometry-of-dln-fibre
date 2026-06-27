# Review - A2 retained-passive dPcast zero solvedA1 substitution

Date: 2026-06-27.

Reviewer: xhigh `Hypatia`.

Verdict: PASS.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`;
- `reproduction-a2-retained-passive-dpcast-zero-solveda1-substitution.md`;
- `statement-card-a2-retained-passive-dpcast-zero-solveda1-substitution.md`.

The review target was
`fderiv_retainedPassive_solvedA1_residualFactorProduct_zero_castSucc_apply`.

## Findings

No findings.

## Checks

- The Lean theorem fixes `p : Fin (M + 1) := 0` and states exactly the scoped
  product-rule specialization with only the zero solved-`A1` derivative
  substituted.
- `dPsucc` and `dTail` remain explicit lets, with `dTail` the actual Frechet
  derivative of `Tfun`.
- Factor order is preserved:

```text
dPsucc * solvedA1(0)
  + Psucc(z) *
      (Tail^-1 * v.Ctop - Tail^-1 * dTail * Tail^-1 * data.Ctop).
```

- The determinant-chart hypothesis is appropriate for the inverse-tail
  derivative dependency, and the typeclass assumptions match the nearby
  solved-`A1` derivative infrastructure.
- The theorem does not claim `Psucc = Tail`, does not expand `dTail`, and does
  not touch `dEarly`, normal crossings, pole order, or RLCT.
- Placement is dependency-forward: the helper follows the generic
  solved-`A1` residual-product product rule and the zero solved-`A1`
  derivative theorem, before downstream lower-left recurrences.

The reviewer did not run Lean; the controller ran the focused builds and
axiom audit separately.
