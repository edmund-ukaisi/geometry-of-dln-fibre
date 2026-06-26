# Statement Card - A2 p.13 regular-coordinate inverse density handoff

## Lean Files

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepMeasure.lean`
- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepRegularDensity.lean`

## Claim

Lean defines the raw-shaped target tuple for the left-endpoint p. 13
multi-edge regular-coordinate family:

```text
(Ctop(u), Dtail(x), F3(u), Ctop(u), F2(u), 0, C0(x)).
```

At a centered self-base point `(x0,0)`, this tuple lies in the product-step
target determinant chart, varies continuously, and therefore the chart-side
inverse product-step Jacobian density is continuous and positive along it.

## Lean Names

```text
continuousAt_productReductionStepRawOrderInverseJacobianDensity_comp_of_mem_rawDetChartSet
productReductionStepRawOrderInverseJacobianDensity_comp_pos_of_mem_rawDetChartSet
paperEndpointFixedBaseP13RawOrderTuple
paperEndpointFixedBaseP13RawOrderTuple_mem_rawDetChartSet
paperEndpointFixedBaseP13RawOrderTuple_mem_rawDetChartSet_center
continuousAt_paperEndpointFixedBaseP13RawOrderTuple_selfBase
continuousAt_paperEndpointFixedBaseP13RawOrderTuple_inverseJacobianDensity_selfBase
paperEndpointFixedBaseP13RawOrderTuple_inverseJacobianDensity_pos_center
```

## Inputs

- A finite paper chain `V`, fixed paper edge family `Bv`, and through subspace
  `U0` complementary to the total kernel.
- A base reversed-edge family `CedgeBase` continuous at `x0`.
- The self-base condition
  `CedgeBase x0 = fun p => LinearMap.toContinuousLinearMap (reverseEdge V Bv p)`.
- The centered regular coordinate `0`.

## Method

The proof decodes `u` into `Ctop`, `F2`, and `F3`, reads `Dtail` and `C0` from
the deterministic suffix recursion applied to the base edge matrices, and
forms the raw-shaped target tuple.  Determinant-chart membership is two copies
of `IsUnit det(Ctop(u))`; at `u = 0`, this is `det I = 1`.

Continuity is fieldwise: regular-coordinate matrix readouts are continuous,
suffix residual products and residual blocks are continuous under self-base
recursive determinant charts, and the `A3` slot is constant zero.  The existing
abstract inverse-density composition theorem then supplies the density
continuity and positivity conclusions.

## Not Proved

This checkpoint does not prove a general arbitrary-step tuple, source
coverage, original DLN source/prior transport, unweighted measure transport,
normal crossings, pole order, or RLCT.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepRegularDensity
```

Full build:

```text
cd lean
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre
```

Both passed on 2026-06-26.  The full build reported only pre-existing warnings
in unrelated files and long-line warnings already present in `DLNFibre.lean`.
