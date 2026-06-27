# Review - A2 retained-passive dEarly dPcast solvedA1 product rule

Date: 2026-06-27.

Reviewer: xhigh `Fermat`.

Verdict: PASS.

## Scope

Reviewed the solved-`A1` residual-product `dPcast` product-rule slice in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

against the reproduction and statement card:

```text
reproduction-a2-retained-passive-dearly-dpcast-solveda1-product-rule.md
statement-card-a2-retained-passive-dearly-dpcast-solveda1-product-rule.md
```

Reviewed Lean name:

```text
fderiv_retainedPassive_solvedA1_residualFactorProduct_castSucc_apply
```

## Findings

No blocking issue.

The theorem proves only the noncommutative product rule for the solved-`A1`
residual product:

```text
dPcast = dPsucc * solvedA1_z(p) + Psucc(z) * d(solvedA1 p).
```

The current solved-factor derivative remains an explicit `fderiv` term; it is
not replaced by a passive source tangent.

The hypotheses are correctly scoped.  The theorem requires the tuple
determinant-chart membership `hz`, and the proof consumes the existing
chart-local differentiability lemmas for solved `A1` and its residual product.
No separate determinant-unit hypothesis is exposed.

The residual-product indices are correct: `Pcast` starts at `p.castSucc`,
`Psucc` starts at `p.succ`, and `residualFactorProduct_castSucc` gives
`Pcast = Psucc * solvedA1 p`.  This is compatible with the downstream
`dEarly` usage where `p := q.castSucc`.

The notes correctly state the nonclaims: no derivative formula for
`solvedA1 0`, no complete `dPcast` source-staging, no downstream Jacobian
import/cycle, no determinant equality, no measure transport, no normal
crossings, no pole order, and no RLCT.

## Verification Notes

The reviewer did not run a build.  Controller verification ran the focused
`scripts/lb` module build, `scripts/sorries`, `git diff --check`, the full
`DLNFibre` build, and theorem axiom audit successfully.  The new theorem has
only the standard `[propext, Classical.choice, Quot.sound]` footprint.
