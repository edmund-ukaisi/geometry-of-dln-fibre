# Statement Card - A2 Retained-Passive Actual Derivative F3 Shear Bridge

Status: reproduced, Lean-proved, and xhigh-reviewed.

## Claim

For a retained-passive tuple `z` in the determinant chart and tangent vector
`v`, the terminal lower-left raw-order component becomes the formal `F3`
component after subtracting the earlier-tail derivative and adding the
terminal-top-factor derivative correction:

```text
((D raw z) v).F3
  - d(Early)(v) * LastTop
  + (coord.F3 - Early) * d(LastTop)(v)
= v.F3 * (-LastTop).
```

Here `raw = topologyTupleEdgeRawOrder`,
`coord = (ofTopologyTuple z).toCoordinateData`,

```text
Early =
  retainedPassiveLowerLeftProductTailSum
    coord.solvedA1 (retainedPassiveA3WithoutLast data.A3seed) coord.C
    0 (Nat.zero_le (M+1)),
```

and

```text
LastTop =
  residualFactorProduct coord.solvedA1
    (Fin.last (M+1)) (Fin.last M).castSucc
    (Fin.last M).castSucc.le_last.
```

The matching sheared `F3` component agrees with the point-specialized formal
raw-order map:

```text
sheared_F3_component ((D raw z) v)
  = (retainedPassiveFormalRawOrderJacobianAt z v).F3.
```

The terminal factor is the final solved top-left block:
`LastTop = coord.solvedA1 (Fin.last M)`.  For `M = 0`, this is `coord.Ctop`,
not an empty identity and not the passive first-edge tail used in the `Ctop`
bridge.

## Lean Status

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

New theorem names:

```text
fderiv_topologyTupleEdgeRawOrder_F3_component_shear_apply
fderiv_topologyTupleEdgeRawOrder_F3_shear_apply
F3_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
```

Focused builds passed locally with `lake build`:

```text
DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative
DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian
```

Full local build passed:

```text
DLNFibre
```

Controller audits passed:

```text
lean/scripts/sorries
git diff --check
#print axioms for the three new theorem names
```

The axiom audit reported only the ordinary classical/quotient axioms
`propext`, `Classical.choice`, and `Quot.sound`.

The shared-cache `lean/scripts/lb` path was unavailable in this sandbox because
the shared Lake slot was read-only; this slice therefore used the local Lake
build requested by the controller.

## Reproduction

```text
reproduction-a2-retained-passive-actual-derivative-f3-shear-bridge.md
```

Independent pen-and-paper check:

```text
Epicurus the 5th, xhigh read-only reviewer, PASS on algebra, signs,
right-multiplication order, `M = 0`, and `LastTop` versus `Tail`.
```

Lean reconnaissance:

```text
Godel the 5th, xhigh read-only scout, PASS on available APIs and target shape.
```

Implementation/orientation review:

```text
Jason the 5th, xhigh read-only explorer, PASS.
review-a2-retained-passive-actual-derivative-f3-shear-bridge.md
```

## Dependencies

- raw terminal lower-left formula `topologyTupleEdgeRawOrder_F3`;
- terminal solve `retainedPassiveSolvedA3_last`;
- differentiability of `F3`, the earlier lower-left tail, and the terminal
  residual factor on `topologyTupleDetChartSet`;
- bilinear product rule for finite matrix multiplication;
- terminal one-edge factor identity
  `retainedPassiveLastTopResidualFactorProduct_eq`;
- formal raw-order apply formula `retainedPassiveFormalRawOrderJacobian_apply`.

## Nonclaims

This proves a sheared terminal component identity only.  It does not prove a
global determinant-one shear linear equivalence, full equality between the
actual Frechet derivative and the formal raw-order map, a signed or absolute
determinant formula, a measure pushforward, source-prior transport,
source-rank coverage, normal crossings, pole order, or RLCT.
