# Review - A2 retained-passive dEarly product-rule dG substitution

Date: 2026-06-27.

Reviewer: xhigh `Averroes`.

Verdict: PASS.

## Scope

Reviewed the proposed `dG` substitution theorem pair in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

against the reproduction and statement card:

```text
reproduction-a2-retained-passive-dearly-product-rule-dg-substitution.md
statement-card-a2-retained-passive-dearly-product-rule-dg-substitution.md
```

## Findings

No blocking issue.

The theorem `fderiv_retainedPassiveA3WithoutLast_apply` correctly packages the
endpoint split for the zeroed-final `A3` family derivative: the passive source
tangent `v.2.2.1 q` on `q.castSucc` and zero at `Fin.last M`.

The theorem
`fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dG_castSucc_apply`
is scoped only to nonterminal `p = q.castSucc` and substitutes only the
`dA3p` factor in the existing product-rule recurrence.

The matrix factor order is preserved:

```text
Cprod * v.2.2.1 q * Pcast^{-1}.
```

The inverse-derivative term remains in the existing product-rule order:

```text
Cprod * A3p * Pcast^{-1} * dPcast * Pcast^{-1}.
```

The reproduction and statement card explicitly avoid target staging,
determinant, measure, normal-crossing, pole-order, and RLCT claims.

## Post-review verification

After the review, `scripts/sorries` reported zero `sorry`, `#exit`,
`native_decide`, and `axiom`; `git diff --check` was clean; the full
`DLNFibre` build succeeded; and the theorem axiom audit reported only the
standard `[propext, Classical.choice, Quot.sound]` footprint for both new
theorems.
