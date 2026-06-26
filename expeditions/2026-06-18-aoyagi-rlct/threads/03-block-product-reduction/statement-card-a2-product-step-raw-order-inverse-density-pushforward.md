# Statement Card - A2 product-step raw-order inverse-density pushforward

## Lean Files

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepMeasure.lean`

## Claim

On the raw determinant chart for the p. 13 product-step coordinate change, the
raw-order map sends unweighted additive Haar measure restricted to the source
determinant chart to additive Haar measure on the raw-shaped target determinant
chart weighted by the chart-side inverse Jacobian density.

In Lean:

```text
Measure.map productReductionStepTopologyTupleToChartRawOrder
  (m.restrict productReductionStepRawDetChartSet)
=
(m.restrict productReductionStepRawDetChartSet).withDensity
  (fun y => ENNReal.ofReal
    (productReductionStepRawOrderInverseJacobianDensity y)).
```

The right-hand restriction is the same raw-shaped determinant chart because the
raw-order product-step map is already proved to map the determinant chart onto
it.

## Lean Names

```text
map_withDensity_comp_of_aemeasurable
productReductionStepRawOrderInverseJacobianDensity_apply_chartMap
productReductionStepRawOrderJacobianAbsDet_mul_inverseJacobianDensity_apply_chartMap
map_productReductionStepRawOrder_restrict_detChart_eq_withDensity_inverseJacobian
```

The first name is private local measure-theory plumbing.

## Inputs

- Finite index types for the product-step raw tuple, with the decidable
  equality instances used by the raw-coordinate inverse-density API
  (`DecidableEq ρ` and `DecidableEq μ` in Lean).
- A Borel measurable raw tuple space.
- An additive Haar measure `m` on that raw tuple space.
- Null-measurability of `productReductionStepRawDetChartSet` for `m`.

## Method

The existing weighted change-of-variables theorem proves

```text
Phi_* ((m|s) with density J) = m|s,
```

where `Phi` is the raw-order product-step map, `s` is the raw determinant chart,
and `J(z)` is the source-side absolute determinant density.

The new pointwise calculation proves on `s` that

```text
productReductionStepRawOrderInverseJacobianDensity (Phi z) = J(z)^(-1),
```

hence

```text
ENNReal.ofReal (J z)
  * ENNReal.ofReal (productReductionStepRawOrderInverseJacobianDensity (Phi z))
= 1.
```

A local generic measure lemma transports a second density through a pushforward:

```text
map f (eta.withDensity (g o f)) = (map f eta).withDensity g.
```

Applying it to the weighted COV identity and then cancelling the product
density gives the unweighted source orientation.

## Not Proved

This is not original DLN source/prior transport.  It does not construct the
p. 13 source chart from original DLN coordinates, prove source coverage,
identify a signed-box source density, produce regular suspension charts,
prove normal crossings, compute pole order, or extract RLCT.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepMeasure
```

passed on 2026-06-26.

Full check:

```text
cd lean
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre
scripts/sorries
git diff --check
```

passed on 2026-06-26.  The sorry scan reported `0 sorry`, `0 #exit`,
`0 native_decide`, and `0 axiom`.
