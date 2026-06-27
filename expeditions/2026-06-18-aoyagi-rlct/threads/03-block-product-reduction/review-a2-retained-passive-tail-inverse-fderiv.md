# Review - A2 Retained-Passive Tail-Inverse Frechet Derivative

Date: 2026-06-27.

Reviewer: xhigh `Epicurus`.

Verdict: PASS.

## Scope Reviewed

Lean:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Theorems:

```text
fderiv_retainedPassive_A1TailAfterFirst_inv_eq_tail_fderiv
Ctop_tail_fderiv_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
```

Reproduction and statement card:

```text
reproduction-a2-retained-passive-tail-inverse-fderiv.md
statement-card-a2-retained-passive-tail-inverse-fderiv.md
```

## Findings

No blocking findings.

The inverse derivative has the correct order and sign:

```text
d(Tail^{-1}) = -(Tail^{-1} * dTail * Tail^{-1}),
```

with `dTail` kept as the actual Frechet derivative of the tail map, not
expanded recursively.

The determinant-unit use is properly scoped.  The proof derives
`IsUnit det(Tail)` from the passive `A1` determinant-chart hypotheses; the
`Ctop` determinant unit is not used for the inverse-tail derivative.

The strengthened Ctop theorem substitutes the previous
`-dTailInv * coord.Ctop` term into the positive term

```text
+ Tail^{-1} * dTail * Tail^{-1} * coord.Ctop
```

with the same multiplication order.

The reproduction and statement card keep the correct nonclaim boundary: no
recursive `dTail` formula, no full `Ctop` source staging, and no determinant
equality, measure, normal-crossing, pole-order, or RLCT claim.

## Reviewer Build Note

The reviewer did not rerun Lean because the review was read-only.  The
controller had already run the focused and full builds for this exact slice.
