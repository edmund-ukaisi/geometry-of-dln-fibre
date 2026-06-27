# Statement Card - A2 retained-passive recursive target-staged lower-left tail

## Claim

The retained-passive zeroed-final lower-left tail now has a recursive
target-staged derivative expression.  The recursion is indexed by the Nat
position in the earlier-tail coordinates, has base value zero at the
zeroed-final tail, and unfolds by the named one-step lower-left core.

## Lean names

```text
retainedPassiveLowerLeftTailCurrentTargetSolvedA1TangentAt
retainedPassiveLowerLeftTailCurrentTargetSolvedA1TangentAt_zero
retainedPassiveLowerLeftTailCurrentTargetSolvedA1TangentAt_succ
retainedPassiveLowerLeftProductTailTargetStagedFDerivAt
retainedPassiveLowerLeftProductTailTargetStagedFDerivAt_self
retainedPassiveLowerLeftProductTailTargetStagedFDerivAt_step
retainedPassiveLowerLeftProductTailTargetStagedFDerivAt_zero
retainedPassiveLowerLeftProductTailTargetStagedFDerivAt_succ
```

## Hypotheses

These are expression and unfold lemmas over the retained-passive raw tuple
space.  They do not require determinant-chart membership because they do not
assert equality with the actual Frechet derivative yet.

## Proof Shape

The current solved-`A1` target tangent is separated from the lower-left
recursion:

- at Nat index `0`, it is
  `Tail^-1 * v.Ctop - Tail^-1 * dTail * Tail^-1 * coord.Ctop`;
- at successor Nat index `s.val + 1`, it is `v.1 s.castSucc`.

The recursive derivative expression is defined by `Nat.decreasingInduction`
with base value `0` at `m = M+1`.  The generic step theorem is the
`Nat.decreasingInduction_succ_left` unfold.  The zero and successor unfold
theorems are the generic step theorem plus the current-tangent simplification.

## Dependencies

- `retainedPassiveLowerLeftTailStepCoreAt`.
- The current solved-`A1` tangent formulas already used by the zero/successor
  step-core wrappers.
- `Nat.decreasingInduction_succ_left`.

## Nonclaims

This does not yet prove that the recursive expression equals the actual
Frechet derivative of `retainedPassiveLowerLeftProductTailSum`.  It does not
plug into the positive-tail `F3` theorem yet.  It does not construct the
target-side determinant-one linear equivalence, prove determinant equality,
source-prior transport, inverse-density pushforward, normal crossings, pole
order, or RLCT.

## Review Focus

- The recursive base must be `m = M+1`, the zeroed-final tail.
- The successor current tangent must be `v.1 s.castSucc`, not `v.1 s.succ`.
- The step must call `retainedPassiveLowerLeftTailStepCoreAt` with the recursive
  successor value as `dNext`.
- The statement must remain an expression/unfold API until a separate theorem
  proves equality with the actual Frechet derivative.
