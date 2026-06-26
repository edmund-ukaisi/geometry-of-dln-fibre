# Review - A2 p.13 raw product-step preimage

Date: 2026-06-26.

## Findings

No correctness or scope issues found in the reviewed slice.

## Checks

- The Lean preimage tuple is exactly the raw source tuple
  `(I,Dtail,F3,Ctop,-Ctop*F2,0,C0)`, with the target tuple
  `(Ctop,Dtail,F3,Ctop,F2,0,C0)` in raw order; see
  `ProductReductionStepRegularDensity.lean` lines 34-92 and 101-159.
- The determinant-chart hypotheses are correct: the raw source chart checks
  `C1 = I` and `A1 = Ctop`, while the target chart checks `Ctop` in both
  determinant slots; see lines 168-218 and 278-327.
- The raw product-step equality proves only the chart algebra
  `Phi(I,Dtail,F3,Ctop,-Ctop*F2,0,C0) =
  (Ctop,Dtail,F3,Ctop,F2,0,C0)`, using only the inverse of `Ctop`; see lines
  386-480.
- The endpoint dimensions are consistent with the product-step tuple
  parameters `rho`, `pi = kappa last`, `mu = kappa 1`, and `nu = kappa 0`:
  `Dtail : pi x mu`, `F3 : pi x rho`, `F2 : rho x nu`,
  `0 : mu x rho`, and `C0 : mu x nu`.
- The reproduction note states the same substitution and determinant condition;
  see `reproduction-a2-p13-raw-product-step-preimage.md` lines 24-66 and its
  nonclaims at lines 91-95.
- The statement card does not overclaim beyond the raw product-chart preimage
  algebra; see `statement-card-a2-p13-raw-product-step-preimage.md` lines 16-24
  and 76-81.

## Source Fidelity

Aoyagi p. 13 transforms the next product-step variables by
`C^(S+1) = -A'_3 A'_1^-1 A'_2 + A'_4`,
`F''_2 = -A'_1^-1 A'_2`, and
`F''_3 = F'_3 - (prod C^(s)) A'_3 (C'_1 A'_1)^-1`.
The Lean theorem specializes this raw algebra to the left-endpoint preimage
with `C1 = I`, `A1 = Ctop`, `A2 = -Ctop*F2`, `A3 = 0`, and `A4 = C0`.

## Boundary

This theorem proves raw product-chart algebra only. It does not assert source
coverage, original DLN source/prior transport, signed-box density, normal
crossings, pole order, or RLCT.

## Verification

Focused Lean check passed:

```text
cd lean
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepRegularDensity
```

Lean emitted flexible-tactic linter warnings at
`ProductReductionStepRegularDensity.lean` line 466 in the equality proof. These
are proof-maintenance warnings, not a mathematical or scope defect in this
reviewed slice.

## Residual Risk

This review did not audit the broader regular-suspension construction, source
coverage, measure transport, signed-box model, normal-crossing extraction, pole
order, or RLCT assembly.
