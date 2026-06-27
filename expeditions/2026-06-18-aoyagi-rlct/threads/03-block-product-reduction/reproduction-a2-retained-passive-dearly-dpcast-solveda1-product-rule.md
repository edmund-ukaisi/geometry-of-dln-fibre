# Reproduction - A2 retained-passive dEarly dPcast solvedA1 product rule

Date: 2026-06-27.

Status: controller pen-and-paper reproduction; Lean target selected.

This note is independent of the quiver-based paper.  It records the next
narrow source-staging step for the retained-passive `dEarly` recurrence: the
product-rule expansion of the solved-`A1` residual product that appears as
`Pcast`.

## Setup

Fix a passive top-left suffix index `p : Fin (M+1)`.  For an ambient tuple
`y`, define

```text
A_s(y) = solvedA1_y(s),
Pcast(y) = residualFactorProduct A(y) final p.castSucc,
Psucc(y) = residualFactorProduct A(y) final p.succ.
```

The determinant-chart hypothesis on the basepoint `z` is retained because
`solvedA1_y(0)` contains the inverse of the top-left tail, so differentiability
of both the current solved factor and the successor product is chart-local.

## Calculation

By the residual-factor unfold,

```text
Pcast(y) = Psucc(y) * A_p(y).
```

Taking the Frechet derivative at `z` in tangent direction `v` gives the
noncommutative product rule

```text
dPcast_z(v)
  = dPsucc_z(v) * A_p(z) + Psucc(z) * dA_p,z(v).
```

In Lean notation,

```text
A_p(z) = ((ofTopologyTuple z).toCoordinateData).solvedA1 p,
dA_p,z(v) =
  (fderiv ℝ (fun y => ((ofTopologyTuple y).toCoordinateData).solvedA1 p) z) v.
```

This is the intended stopping point.  The derivative `dA_p,z(v)` is not a
uniform passive source tangent:

- if `p = 0`, the factor is the solved endpoint
  `tail(A1seed)^{-1} * Ctop`;
- if `p = q.succ`, its source-coordinate derivative is indexed by the
  corresponding stored `A1seed` position, not by the same index as the
  surrounding `dEarly` current `q` in general.

## Lean Scope

Planned Lean addition in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`:

```text
fderiv_retainedPassive_solvedA1_residualFactorProduct_castSucc_apply
```

The proof should mirror the existing stored-`C` suffix helper:

```text
fderiv_retainedPassive_C_residualFactorProduct_castSucc_apply
```

but use `differentiableAt_residualFactorProduct_solvedA1_of_mem_topologyTupleDetChartSet`
and `differentiableAt_solvedA1_of_mem_topologyTupleDetChartSet`, and leave the
current solved-factor derivative explicit.

## Kill Conditions

- If the theorem replaces `dA_p,z(v)` by a passive source tangent for all `p`,
  it is wrong.
- If the theorem imports downstream Jacobian recovery results into
  `RetainedPassiveCoordinatesDerivative.lean`, it risks an import cycle and is
  outside this slice.
- If the factor order changes from
  `dPsucc * A_p + Psucc * dA_p`, it is not the intended noncommutative product
  rule.
- If this theorem is advertised as source-staging `dPcast` completely, target
  staging, determinant equality, measure transport, normal crossings, pole
  order, or RLCT, it overclaims.

## Nonclaims

No derivative formula for `solvedA1 0`, no full source-staging of `dPcast`, no
closed finite-sum formula, no target staging, no determinant theorem, no
measure theorem, no normal crossings, no pole order, and no RLCT follows from
this product-rule slice.
