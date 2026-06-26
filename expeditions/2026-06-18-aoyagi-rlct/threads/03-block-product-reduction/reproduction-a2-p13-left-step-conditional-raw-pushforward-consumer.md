# Reproduction - A2 p.13 left-step conditional raw pushforward consumer

Date: 2026-06-26.

Status: Lean proved.

## Question

We have proved the raw product-step pushforward theorem on the determinant
chart and the pointwise p.13 identity

```text
Phi(X(x,u)) = Y(x,u),
```

where

```text
X(x,u) = (I,Dtail(x),F3(u),Ctop(u),-Ctop(u)*F2(u),0,C0(x))
Y(x,u) = (Ctop(u),Dtail(x),F3(u),Ctop(u),F2(u),0,C0(x)).
```

The next safe consumer should not claim that the original p.13 source measure
pushes forward to the raw determinant-chart Haar measure.  It should instead
take that as an explicit hypothesis and only compose the already-proved raw
product-step pushforward.

The reason is not merely a missing API.  The p.13 raw preimage is a section of
the full raw tuple space: its raw `C1` coordinate is fixed to `I` and its raw
`A3` coordinate is fixed to `0`.  In nontrivial raw `C1` or `A3` directions,
this is lower-dimensional inside the full raw determinant chart, so p.13 does
not support a full raw-Haar pushforward theorem for `X`.

## Pen-and-Paper Check

Let `η` be a measure on the p.13 parameter space and let `m` be an additive
Haar measure on the raw tuple space.  Let `S` be the raw determinant chart and
let `Phi` be the raw-order product-step map.

Assume explicitly that the raw preimage map has the required pushforward:

```text
map X η = m|S.
```

Since `m|S` is supported on `S`, functorial support gives

```text
X(x,u) ∈ S for η-almost every (x,u).
```

The second raw determinant-chart condition in `S` is the unit condition on the
`A1` block.  For the p.13 raw preimage tuple, that block is `Ctop(u)`, hence

```text
IsUnit det(Ctop(u))
```

holds for `η`-almost every `(x,u)`.  Thus the determinant-unit hypothesis
needed for the pointwise p.13 product-step identity is not an additional input
once the raw-chart pushforward and raw-map a.e. measurability are supplied.

The raw product-step theorem gives

```text
map Phi (m|S)
  = (m|S).withDensity (ofReal K),
```

where `K` is the chart-side inverse Jacobian density.

By functoriality of measure pushforward,

```text
map (Phi ∘ X) η = map Phi (map X η).
```

Using the supplied raw-preimage pushforward hypothesis,

```text
map (Phi ∘ X) η
  = (m|S).withDensity (ofReal K).
```

The derived determinant-unit fact lets us apply the pointwise p.13 calculation
almost everywhere, giving `Phi(X(x,u)) = Y(x,u)`, hence

```text
map Y η
  = (m|S).withDensity (ofReal K).
```

This is the intended theorem.

## Lean Shape

Lean added a generic raw-product-step composition consumer:

```text
aemeasurable_productReductionStepTopologyTupleToChartRawOrder_restrict_detChart
ae_mem_productReductionStepRawDetChartSet_of_map_eq_restrict
map_productReductionStepRawOrder_comp_eq_withDensity_inverseJacobian
paperEndpointFixedBaseP13RawPreimageTuple_C1_eq_one
paperEndpointFixedBaseP13RawPreimageTuple_A3_eq_zero
p13ProductCoordinateLeftStepRawTopologyTuple_C1_eq_one
p13ProductCoordinateLeftStepRawTopologyTuple_A3_eq_zero
ae_isUnit_ctopMatrix_det_of_p13RawPreimage_map_eq_restrict_rawDetChart
ae_isUnit_ctopMatrix_det_of_p13LeftStepRaw_map_eq_restrict_rawDetChart
```

with inputs:

```text
hpre       : AEMeasurable pre η
hpre_map   : Measure.map pre η = m.restrict S
```

and conclusion:

```text
Measure.map (fun x => Phi (pre x)) η
  =
(m.restrict S).withDensity (fun y => ofReal (inverseJacobianDensity y)).
```

The raw determinant chart is open, hence null-measurable for the Borel Haar
measure.  Since `Phi` is continuous on the raw determinant chart and
`map pre η = m|S`, the a.e.-measurability of `Phi` for `map pre η` is derived
inside the theorem rather than supplied by the caller.

It then specializes this first to the explicit p.13 raw preimage tuple:

```text
map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_rawPreimage_map
```

and then to the actual constructed left-step raw tuple:

```text
p13ProductCoordinateLeftStepRawTopologyTuple
map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_leftStepRaw_map
```

Both p.13 theorems derive the almost-everywhere determinant-unit fact for
`Ctop(u)` from the supplied raw pushforward and raw-map a.e. measurability.
The public left-step theorem takes the supplied pushforward hypothesis for the
actual constructed left-step raw tuple.

## Kill Conditions

- If the theorem asserts `map X η = m|S` without a hypothesis, it overclaims.
- If the theorem treats the p.13 section as full-dimensional raw-Haar chart
  data, it contradicts the formal section facts `C1 = I` and `A3 = 0`.
- If the theorem mentions original DLN source coverage or prior transport in
  the conclusion, it overclaims.
- If it requires an inverse of `Dtail`, the statement is wrong.

## Nonclaims

No original DLN source chart, no source coverage, no source/prior transport,
no signed-box density identification, no product-measure pushforward, no
regular-suspension certificate, no normal crossings, no pole order, and no
RLCT.
