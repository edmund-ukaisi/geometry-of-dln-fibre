# Statement Card - A2 retained-passive F3 recursive dEarly plug-in

## Claim

For a positive retained-passive tail, the terminal `F3` bridge can use the
recursive target-staged lower-left derivative as its `dEarly` term.

## Lean names

```text
F3_tail_pos_recursive_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F3_tail_pos_recursive_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
```

## Hypotheses

The theorems assume determinant-chart membership

```text
z ∈ topologyTupleDetChartSet
```

for

```text
z : RetainedPassiveRawTopologyTuple (M := M+1) ρ κ' ℝ,
κ' : Fin ((M+1)+2) -> Type*.
```

They are stated for an arbitrary tangent `v`.  The positive tail supplies
`qLast : Fin (M+1) := Fin.last M`, and the first lower-left tail derivative is
the recursive value

```text
retainedPassiveLowerLeftProductTailTargetStagedFDerivAt
  (M := M) (ρ := ρ) (κ' := κ') z v 0 (Nat.zero_le (M+1)).
```

## Proof Shape

The equality theorem starts from the existing terminal-target-staged positive
tail `F3` bridge at `qLast`, where `qLast.succ = Fin.last (M+1)` by `rfl`.
It then rewrites the actual derivative `(fderiv Earlyfun z) v` by the landed
actual-derivative bridge

```text
fderiv_retainedPassiveLowerLeftProductTailSum_targetStaged_apply
```

at index `m = 0`.  The proof only changes the `dEarly` slot and preserves the
displayed product order.

The recovery theorem composes the same component equality with

```text
retainedPassiveFormalRawOrderJacobianAt_recovers_F3
```

and right-multiplies by

```text
(-(coord.solvedA1 (Fin.last (M+1))))^-1.
```

## Dependencies

- `F3_tail_pos_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`.
- `fderiv_retainedPassiveLowerLeftProductTailSum_targetStaged_apply`.
- `retainedPassiveFormalRawOrderJacobianAt_recovers_F3`.

## Nonclaims

This is the recursive positive-tail `F3` plug-in only.  It does not delete the
older finite-unroll compatibility lemmas, construct the determinant-one target
normalizer, prove determinant equality, prove source-prior transport,
inverse-density pushforward, normal crossings, pole order, or RLCT.

## Review Focus

- The theorem is for raw tail parameter `M+1`, but the recursive derivative is
  called with `(M := M)`.
- `qLast.succ` must be `Fin.last (M+1)`.
- `Earlyfun` must syntactically match the `m = 0` instance of the lower-left
  product-tail derivative bridge.
- The recovery factor is the inverse of `-(coord.solvedA1 (Fin.last (M+1)))`.
- No noncommutative matrix factors may be commuted.
