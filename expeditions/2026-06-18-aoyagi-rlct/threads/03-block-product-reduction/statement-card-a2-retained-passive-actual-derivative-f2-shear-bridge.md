# Statement Card - A2 Retained-Passive Actual Derivative F2 Shear Bridge

Status: reproduced, Lean-proved, and xhigh-reviewed.

## Claim

For a retained-passive tuple `z` in the determinant chart, tangent vector `v`,
and edge `p : Fin (M+1)`, the actual Frechet derivative of the raw-order map
has the expected upper-right block after the top-left and successor-`F2`
shear corrections:

```text
((D raw z) v).F2 p
  + rawEdgeTupleA1 ((D raw z) v) p * coord.F2 p.castSucc
  - d(coord.F2 p.succ)(v) * coord.C p
= -(coord.solvedA1 p + coord.F2 p.succ * coord.solvedA3 p) * v.F2 p
  + coord.F2 p.succ * v.C p.
```

Here `raw = topologyTupleEdgeRawOrder`,
`coord = (ofTopologyTuple z).toCoordinateData`, and `D raw z` is the ambient
Frechet derivative `fderiv R raw z`.

The matching sheared `F2` component agrees with the point-specialized formal
raw-order map:

```text
sheared_F2_component ((D raw z) v)
  = (retainedPassiveFormalRawOrderJacobianAt z v).F2 p.
```

The `coord.F2 p.succ` term uses the full `F2full` endpoint convention.  At the
terminal edge, it is the zero matrix and its derivative is zero.

## Lean Status

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

New theorem names:

```text
fderiv_topologyTupleEdgeRawOrder_F2_component_shear_apply
fderiv_topologyTupleEdgeRawOrder_F2_shear_apply
F2_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
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
reproduction-a2-retained-passive-actual-derivative-f2-shear-bridge.md
```

Independent pen-and-paper check:

```text
Lorentz the 5th, xhigh read-only explorer, PASS on algebra and endpoint convention.
```

Implementation review:

```text
Anscombe the 5th, xhigh read-only implementation reviewer, PASS.
review-a2-retained-passive-actual-derivative-f2-shear-bridge.md
```

## Dependencies

- raw upper-right formula `topologyTupleEdgeRawOrder_F2`;
- raw top-left readout `rawEdgeTupleA1`, `rawEdgeTupleA1_zero`,
  `rawEdgeTupleA1_succ`;
- differentiability of `solvedA1`, `solvedA3`, `F2full`, and `C` on
  `topologyTupleDetChartSet`;
- projection of the full Frechet derivative through raw `F2` and raw top-left
  coordinates;
- bilinear product rule for finite matrix multiplication;
- formal raw-order apply formula `retainedPassiveFormalRawOrderJacobian_apply`.

## Nonclaims

This proves a sheared component identity only.  It does not prove a global
determinant-one shear linear equivalence, full equality between the actual
Frechet derivative and the formal raw-order map, a signed or absolute
determinant formula, a measure pushforward, source-prior transport,
source-rank coverage, normal crossings, pole order, or RLCT.
