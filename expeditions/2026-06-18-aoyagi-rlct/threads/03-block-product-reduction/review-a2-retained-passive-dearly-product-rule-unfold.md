# Review - A2 retained-passive dEarly product-rule unfold

Date: 2026-06-27.

Reviewer: xhigh `Wegener`.

Verdict: PASS.

## Scope

Reviewed the new Lean theorem in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

against the reproduction and statement card:

```text
reproduction-a2-retained-passive-dearly-product-rule-unfold.md
statement-card-a2-retained-passive-dearly-product-rule-unfold.md
```

## Findings

No blocking issue.

The theorem `fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_apply`
matches the intended product-rule expansion:

```text
-dCprod * A3p * Pcast^-1
-Cprod * dA3p * Pcast^-1
+Cprod * A3p * Pcast^-1 * dPcast * Pcast^-1
+dNext.
```

The theorem uses `retainedPassiveA3WithoutLast` for `A3p`, not the solved
terminal lower-left block.  It preserves the noncommutative matrix order,
including the inverse derivative order `-P^-1 * dP * P^-1`.

The theorem is tied back to the recursive derivative unfold
`fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_apply`.  It does not
claim source staging, target staging, a Jacobian determinant formula, measure
transport, normal crossings, pole order, or RLCT.

The focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` passed before this
review.
