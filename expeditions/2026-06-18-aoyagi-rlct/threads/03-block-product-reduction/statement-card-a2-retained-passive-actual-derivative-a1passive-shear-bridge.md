# Statement Card - A2 Retained-Passive Actual Derivative Passive A1 Shear Bridge

Status: reproduced, Lean-proved, and xhigh-reviewed.

## Claim

For a retained-passive tuple `z` in the determinant chart, tangent vector `v`,
and passive top-left index `p : Fin M`, the actual Frechet derivative of the
raw-order map has the expected passive top-left component after subtracting
the successor-`F2`/lower-left product corrections:

```text
((D raw z) v).A1passive p
  - d(coord.F2 p.succ.succ)(v) * coord.solvedA3 p.succ
  - coord.F2 p.succ.succ * d(coord.solvedA3 p.succ)(v)
= v.A1passive p.
```

Here `raw = topologyTupleEdgeRawOrder`,
`coord = (ofTopologyTuple z).toCoordinateData`, and `D raw z` is the ambient
Frechet derivative `fderiv R raw z`.

The matching sheared passive `A1` component agrees with the point-specialized
formal raw-order map:

```text
sheared_A1passive_component ((D raw z) v)
  = (retainedPassiveFormalRawOrderJacobianAt z v).A1passive p.
```

The `coord.F2 p.succ.succ` term uses the full `F2full` endpoint convention.
At the terminal passive top-left index, this successor coefficient is the
terminal zero matrix and its derivative is zero.

## Lean Status

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

New theorem names:

```text
fderiv_topologyTupleEdgeRawOrder_A1passive_component_shear_apply
fderiv_topologyTupleEdgeRawOrder_A1passive_shear_apply
A1passive_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
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
reproduction-a2-retained-passive-actual-derivative-a1passive-shear-bridge.md
```

Independent pen-and-paper check:

```text
Herschel the 5th, xhigh read-only explorer, PASS on algebra and endpoint convention.
```

Implementation review:

```text
Nash the 5th, xhigh read-only implementation reviewer, PASS.
review-a2-retained-passive-actual-derivative-a1passive-shear-bridge.md
```

## Dependencies

- raw passive top-left formula `topologyTupleEdgeRawOrder_A1passive`;
- nonzero solve rule `retainedPassiveSolvedA1_eq_of_ne_zero`;
- passive seed readout `A1seed_succ`;
- differentiability of `F2full` and `solvedA3` on
  `topologyTupleDetChartSet`;
- projection of the full Frechet derivative through the passive top-left
  coordinate;
- bilinear product rule for finite matrix multiplication;
- formal raw-order apply formula `retainedPassiveFormalRawOrderJacobian_apply`.

## Nonclaims

This proves a sheared passive-component identity only.  It does not cover the
first top-left `Ctop` coordinate, the terminal lower-left `F3` coordinate, a
global determinant-one shear linear equivalence, full equality between the
actual Frechet derivative and the formal raw-order map, a signed or absolute
determinant formula, a measure pushforward, source-prior transport,
source-rank coverage, normal crossings, pole order, or RLCT.
