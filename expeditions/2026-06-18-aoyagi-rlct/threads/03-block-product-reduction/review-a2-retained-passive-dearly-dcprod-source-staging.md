# Review - A2 retained-passive dEarly dCprod source staging

Date: 2026-06-27.

Reviewer: xhigh `Lovelace`.

Verdict: PASS.

## Scope

Reviewed the new retained-passive `dCprod` source-staging slice in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

against the reproduction and statement card:

```text
reproduction-a2-retained-passive-dearly-dcprod-source-staging.md
statement-card-a2-retained-passive-dearly-dcprod-source-staging.md
```

Reviewed Lean names:

```text
fderiv_retainedPassive_C_apply
fderiv_retainedPassive_C_residualFactorProduct_castSucc_apply
fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dCprod_dG_castSucc_apply
```

## Findings

No blocking issue.

The projection derivative theorem for the stored `C` coordinate matches the
`TopologyTuple` layout.  The residual-product recurrence preserves the
noncommutative order from `residualFactorProduct_castSucc`: successor product
on the left, current `C` block on the right.

The `q.castSucc`/`q.succ` split in the final theorem is correct.  The lower-
left tail current edge is `p = q.castSucc`, but the first stored `C` edge in
`Cprod` is `r = q.succ`, because `p.succ` is represented as `r.castSucc`.
Thus the source tangent is `v.2.2.2.1 r`, not `v.2.2.2.1 p`.

The substituted `dCprod` expression remains the leftmost factor inside
`-((...) * A3p * Pcast^-1)`.  The already-staged `dG` term and the
inverse-derivative term keep the order from the previous product-rule theorem.

The theorem leaves the successor `C`-product derivative explicit and does not
claim `dPcast` staging, a closed finite-sum formula, target staging,
determinant equality, measure transport, normal crossings, pole order, or
RLCT.

## Verification Notes

The reviewer independently reported a focused Lean check and whitespace check.
Controller verification additionally ran the focused `scripts/lb` module
build, full `DLNFibre` build, `scripts/sorries`, `git diff --check`, and axiom
audit for the three new theorem names.
