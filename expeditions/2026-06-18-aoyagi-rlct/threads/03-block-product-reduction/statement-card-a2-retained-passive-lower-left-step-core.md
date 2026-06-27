# Statement Card - A2 retained-passive lower-left step core

## Claim

The retained-passive lower-left product-tail derivative recurrence has a named
one-step RHS helper.  The helper packages the current `dEarly` product-rule
step after the `dCprod`, `dG`, and `dPcast` staging, while leaving three inputs
explicit:

```text
dAcur   = current solved-A1 tangent,
dPsucc  = suffix solved-A1 product tangent,
dNext   = recursive successor-tail derivative.
```

The generic, zero-current, and successor-current derivative recurrence theorems
are restated through this helper.

## Lean names

```text
retainedPassiveLowerLeftTailStepCoreAt
fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dCprod_dG_dPcast_stepCore_apply
fderiv_retainedPassiveLowerLeftProductTailSum_zero_product_dCprod_dG_dPcast_stepCore_apply
fderiv_retainedPassiveLowerLeftProductTailSum_succ_product_dCprod_dG_dPcast_stepCore_apply
```

## Hypotheses

The three recurrence theorems use the same determinant-chart hypothesis as the
already-proved derivative recurrence they restate:

```text
z in topologyTupleDetChartSet.
```

The helper itself is an expression-valued definition and carries no chart
hypothesis.

## Proof Shape

Each theorem is a definitional restatement of an existing proved theorem:

- the generic wrapper restates the already-proved recurrence with the current
  solved-`A1` derivative left explicit;
- the zero-current wrapper supplies
  `Tail^-1 * v.Ctop - Tail^-1 * dTail * Tail^-1 * coord.Ctop` as `dAcur`;
- the successor-current wrapper supplies `v.1 s.castSucc` as `dAcur`.

No new matrix algebra is introduced.

## Dependencies

- `fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dCprod_dG_dPcast_castSucc_apply`
- `fderiv_retainedPassiveLowerLeftProductTailSum_zero_product_dCprod_dG_dPcast_apply`
- `fderiv_retainedPassiveLowerLeftProductTailSum_succ_product_dCprod_dG_dPcast_apply`

## Nonclaims

This does not define the full Nat-recursive target-staged lower-left
derivative.  It does not construct the target-side determinant-one linear
equivalence.  It does not prove determinant equality, source-prior transport,
inverse-density pushforward, normal crossings, pole order, or RLCT.

## Review Focus

- The successor wrapper must use `v.1 s.castSucc`, not `v.1 s.succ`.
- `dG` remains the lower-left free-block tangent `v.2.2.1 q`, not the `C`
  tangent.
- The helper must preserve the noncommutative order
  `Cprod * A3p * Pcast^-1 * (...) * Pcast^-1`.
- The wrapper theorems must be restatements of existing recurrence theorems,
  not independent algebraic rewrites.
