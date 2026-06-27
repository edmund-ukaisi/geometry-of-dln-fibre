# Statement Card - A2 Retained-Passive Actual Derivative Ctop Shear Bridge

Status: reproduced, Lean-proved, and xhigh-reviewed.

## Claim

For a retained-passive tuple `z` in the determinant chart and tangent vector
`v`, the actual Frechet derivative of the raw-order map has the expected first
top-left component after subtracting the successor-`F2`/lower-left product
derivative and the passive-tail inverse correction:

```text
((D raw z) v).Ctop
  - d(coord.F2 ((0 : Fin (M+1)).succ))(v) * coord.solvedA3 0
  - coord.F2 ((0 : Fin (M+1)).succ) * d(coord.solvedA3 0)(v)
  - d(Tail^{-1})(v) * coord.Ctop
= Tail^{-1} * v.Ctop.
```

Here `raw = topologyTupleEdgeRawOrder`,
`coord = (ofTopologyTuple z).toCoordinateData`, `D raw z` is the ambient
Frechet derivative `fderiv R raw z`, and
`Tail = retainedPassiveA1TailAfterFirst (ofTopologyTuple z).A1seed`.

The matching sheared `Ctop` component agrees with the point-specialized formal
raw-order map:

```text
sheared_Ctop_component ((D raw z) v)
  = (retainedPassiveFormalRawOrderJacobianAt z v).Ctop.
```

The successor `F2` coefficient uses the full `F2full` endpoint convention.
When `M = 0`, this is the terminal zero slot.

## Lean Status

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

New theorem names:

```text
fderiv_topologyTupleEdgeRawOrder_Ctop_component_shear_apply
fderiv_topologyTupleEdgeRawOrder_Ctop_shear_apply
Ctop_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
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

## Reproduction

```text
reproduction-a2-retained-passive-actual-derivative-ctop-shear-bridge.md
```

Independent pen-and-paper check:

```text
Einstein the 5th, xhigh read-only reviewer, PASS on algebra, endpoint slot,
and formal target.
```

Implementation review:

```text
Bohr the 5th, xhigh read-only implementation reviewer, PASS.
review-a2-retained-passive-actual-derivative-ctop-shear-bridge.md
```

## Dependencies

- raw first top-left formula `topologyTupleEdgeRawOrder_Ctop`;
- first solved top-left formula `retainedPassiveSolvedA1_zero`;
- passive tail determinant-unit theorem
  `retainedPassiveA1TailAfterFirst_det_isUnit_of_passive`;
- differentiability of `retainedPassiveA1TailAfterFirst`, matrix inverse,
  `Ctop`, `F2full`, and `solvedA3` on `topologyTupleDetChartSet`;
- projection of the full Frechet derivative through the raw `Ctop`
  coordinate;
- bilinear product rule for finite matrix multiplication;
- formal raw-order apply formula `retainedPassiveFormalRawOrderJacobian_apply`.

## Nonclaims

This proves a sheared first-top-left component identity only.  It does not
cover the passive `A1` bridge, the terminal lower-left `F3` coordinate, a
global determinant-one shear linear equivalence, full equality between the
actual Frechet derivative and the formal raw-order map, a signed or absolute
determinant formula, a measure pushforward, source-prior transport,
source-rank coverage, normal crossings, pole order, or RLCT.
