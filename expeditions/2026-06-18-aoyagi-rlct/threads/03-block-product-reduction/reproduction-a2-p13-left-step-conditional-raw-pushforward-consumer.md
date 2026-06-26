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

## Pen-and-Paper Check

Let `η` be a measure on the p.13 parameter space and let `m` be an additive
Haar measure on the raw tuple space.  Let `S` be the raw determinant chart and
let `Phi` be the raw-order product-step map.

Assume explicitly that the raw preimage map has the required pushforward:

```text
map X η = m|S.
```

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

If `det Ctop(u)` is a unit for `η`-almost every `u`, then the pointwise p.13
calculation gives `Phi(X(x,u)) = Y(x,u)` almost everywhere, hence

```text
map Y η
  = (m|S).withDensity (ofReal K).
```

This is the intended theorem.

## Lean Shape

Lean added a generic raw-product-step composition consumer:

```text
map_productReductionStepRawOrder_comp_eq_withDensity_inverseJacobian
```

with inputs:

```text
hpre       : AEMeasurable pre η
hPhi       : AEMeasurable Phi (Measure.map pre η)
hpre_map   : Measure.map pre η = m.restrict S
```

and conclusion:

```text
Measure.map (fun x => Phi (pre x)) η
  =
(m.restrict S).withDensity (fun y => ofReal (inverseJacobianDensity y)).
```

It then specialized this first to the explicit p.13 raw preimage tuple:

```text
map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_rawPreimage_map
```

and then to the actual constructed left-step raw tuple:

```text
p13ProductCoordinateLeftStepRawTopologyTuple
map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_leftStepRaw_map
```

Both p.13 theorems use the additional almost-everywhere determinant-unit
hypothesis for `Ctop(u)`.  The public left-step theorem takes the supplied
pushforward hypothesis for the actual constructed left-step raw tuple.

## Kill Conditions

- If the theorem asserts `map X η = m|S` without a hypothesis, it overclaims.
- If the theorem mentions original DLN source coverage or prior transport in
  the conclusion, it overclaims.
- If it requires an inverse of `Dtail`, the statement is wrong.

## Nonclaims

No original DLN source chart, no source coverage, no source/prior transport,
no signed-box density identification, no product-measure pushforward, no
regular-suspension certificate, no normal crossings, no pole order, and no
RLCT.
