# Statement Card - A2 retained-passive lower-left target-staged actual derivative bridge

## Claim

On the retained-passive determinant chart, the actual Frechet derivative of the
zeroed-final lower-left product tail is exactly the recursive target-staged
expression.

## Lean name

```text
fderiv_retainedPassiveLowerLeftProductTailSum_targetStaged_apply
```

## Hypotheses

The theorem assumes determinant-chart membership

```text
z ∈ topologyTupleDetChartSet
```

for the retained-passive topology tuple.  It is stated for
`κ' : Fin ((M+1)+2) -> Type*`, a tangent `v`, and a staged tail index
`m ≤ M+1`.

## Proof Shape

The proof uses decreasing induction over the Nat tail index.

- Base `m = M+1`: the zeroed-final tail is the constant zero map, so its
  derivative is zero; this matches
  `retainedPassiveLowerLeftProductTailTargetStagedFDerivAt_self`.
- Step `m = 0`: the zero-current one-step recurrence is rewritten through
  `retainedPassiveLowerLeftTailStepCoreAt`, and the induction hypothesis
  replaces only the successor `dNext` slot.
- Step `m = s.val + 1`: the successor-current recurrence is treated the same
  way; the current solved-`A1` tangent is `v.1 s.castSucc`.

The explicit product tail has one extra zeroed-final slot, so the tail-sum
bound in the actual derivative side is widened from staged `m ≤ M+1` to
`m ≤ M+2`.

## Dependencies

- `fderiv_retainedPassiveLowerLeftProductTailSum_withoutLast_last_apply`.
- `fderiv_retainedPassiveLowerLeftProductTailSum_zero_product_dCprod_dG_dPcast_stepCore_apply`.
- `fderiv_retainedPassiveLowerLeftProductTailSum_succ_product_dCprod_dG_dPcast_stepCore_apply`.
- `retainedPassiveLowerLeftProductTailTargetStagedFDerivAt_zero`.
- `retainedPassiveLowerLeftProductTailTargetStagedFDerivAt_succ`.

## Nonclaims

This does not plug the recursive derivative into the positive-tail `F3`
bridge yet.  It does not construct the target-side determinant-one linear
equivalence, prove determinant equality, source-prior transport,
inverse-density pushforward, normal crossings, pole order, or RLCT.

## Review Focus

- The staged target index is `m ≤ M+1`; the actual tail-sum bound is the
  widened `m ≤ M+2`.
- The base is the zeroed-final tail at `m = M+1`, not a terminal solved
  lower-left block.
- The zero branch must use the solved top-left tangent
  `Tail^-1 * v.Ctop - Tail^-1 * dTail * Tail^-1 * coord.Ctop`.
- The successor branch must use `v.1 s.castSucc`, not `v.1 s.succ` or
  `v.1 q`.
