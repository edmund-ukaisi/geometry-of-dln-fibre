# Review - A2 retained-passive dEarly recursive unfold

Date: 2026-06-27.

Reviewer: xhigh `Faraday`.

Verdict: PASS.

## Scope

Reviewed the new Lean theorem in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

against the reproduction and statement card:

```text
reproduction-a2-retained-passive-dearly-recursive-unfold.md
statement-card-a2-retained-passive-dearly-recursive-unfold.md
```

## Findings

No blocking issue.

The theorem `fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_apply`
matches the safe minimal recursive derivative unfold:

- `p : Fin (M + 1)` is arbitrary.
- The determinant-chart hypothesis remains explicit.
- The current summand derivative is kept as an explicit `fderiv` of
  `fun y => -(Cprod y * A3p y * (Pcast y)^-1)`.
- The successor-tail derivative remains explicit.
- `A3p` is built from `retainedPassiveA3WithoutLast`, not from the solved
  terminal lower-left block.
- No source staging, target staging, determinant equality, measure transport,
  normal crossings, pole order, or RLCT is claimed.

The focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` passed before this
review.
