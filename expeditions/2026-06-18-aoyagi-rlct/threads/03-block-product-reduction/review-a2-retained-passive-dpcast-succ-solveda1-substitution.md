# Review - A2 retained-passive dPcast successor solvedA1 substitution

Date: 2026-06-27.

Reviewer: xhigh `Banach`.

Verdict: PASS.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`;
- `reproduction-a2-retained-passive-dpcast-succ-solveda1-substitution.md`;
- `statement-card-a2-retained-passive-dpcast-succ-solveda1-substitution.md`.

The review target was
`fderiv_retainedPassive_solvedA1_residualFactorProduct_succ_castSucc_apply`.

## Findings

No findings.

## Checks

- The Lean theorem fixes `p := q.succ`, with `Pcast` starting at
  `p.castSucc` and `Psucc` starting at `p.succ`.
- The conclusion matches the reproduced formula:

```text
dPcast_z(v)
  = dPsucc_z(v) * solvedA1_z(p) + Psucc(z) * v.1 q.
```

- The determinant-chart hypothesis is inherited from the generic product-rule
  helper; the successor solved-`A1` derivative itself remains chart-free.
- Factor order is preserved: the substituted term is `Psucc(z) * v.1 q`, not
  a commuted product.
- The tangent is exactly `v.1 q`; no successor-indexed tangent appears.
- `dPsucc` remains explicit, and the theorem does not claim downstream
  `dEarly`, terminal cleanup, determinant or measure transport, normal
  crossings, pole order, or RLCT.
- Placement is dependency-forward: generic product rule, zero specialization,
  then successor specialization, before downstream recurrence wrappers.

The reviewer did not run Lean; the controller ran the focused builds and
axiom audit separately.
