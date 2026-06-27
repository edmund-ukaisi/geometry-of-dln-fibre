# Review - A2 Retained-Passive Tail Product Frechet Derivative Recursion

Date: 2026-06-27.

Reviewer: xhigh `Schrodinger`.

Verdict: PASS after documentation wording fix.

## Scope Reviewed

Lean:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

Theorems:

```text
differentiableAt_retainedPassiveA1seed_residualFactorProduct
fderiv_retainedPassive_A1seed_residualFactorProduct_self_apply
fderiv_retainedPassive_A1seed_residualFactorProduct_succ_castSucc_apply
```

Reproduction and statement card:

```text
reproduction-a2-retained-passive-tail-product-fderiv-recursion.md
statement-card-a2-retained-passive-tail-product-fderiv-recursion.md
```

## Finding And Fix

The first review found one documentation defect: the Lean theorem and displayed
formula correctly used

```text
P_{p.succ}(z) * v.A1passive_q,
```

but the prose said the new source tangent was right-multiplied by the suffix
product.  That reverses the noncommutative order.  The reproduction now says
that the suffix product `P_{p.succ}(z)` left-multiplies the source tangent.

## Accepted Content

The reviewer found no Lean defect after that correction.  The index orientation
is correct, `Tail` starts at `1` and excludes the dummy `A1seed 0`, and the
recursive theorem rewrites the derivative of `A1seed(q.succ)` to the source
tangent `v.1 q`.

The slice does not overclaim determinant-chart hypotheses, a closed finite-sum
formula, inverse-tail differentiation, measure transport, determinant equality,
normal crossings, pole order, or RLCT.
