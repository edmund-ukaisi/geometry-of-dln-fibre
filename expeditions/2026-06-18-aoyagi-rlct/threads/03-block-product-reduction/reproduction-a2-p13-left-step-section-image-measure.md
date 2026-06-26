# Reproduction - A2 p.13 left-step section-image measure

Date: 2026-06-26.

Status: Lean proved; xhigh review pending at creation.

## Source Boundary

Aoyagi p.13 performs elementary block-product reduction.  It displays the
regular block variables and the residual block after triangular row/column
operations, then states the analytic LCT shift.  It does not state a full
Lebesgue/Haar pushforward theorem from the p.13 section to the ambient raw
determinant chart.

The p.13 raw source tuple has the section shape

```text
X(x,u) = (I,Dtail(x),F3(u),Ctop(u),-Ctop(u)*F2(u),0,C0(x)).
```

Thus raw `C1` is fixed to `I` and raw `A3` is fixed to `0`.  In nontrivial
directions this is positive-codimension inside the full raw tuple space, so it
cannot be used to prove

```text
Measure.map X eta = m.restrict rawDetChart
```

for full raw Haar measure `m`.

## Pen-and-Paper Check

Let

```text
Phi
```

be the raw-order product-step map.  On the determinant chart, the already
proved pointwise p.13 algebra gives

```text
Phi(X(x,u)) = Y(x,u),
```

where

```text
Y(x,u) = (Ctop(u),Dtail(x),F3(u),Ctop(u),F2(u),0,C0(x)).
```

For any source measure `eta`, if `X(x,u)` lies in the raw determinant chart
for `eta`-almost every `(x,u)`, then the two maps are equal almost everywhere:

```text
Y = Phi ∘ X      eta-a.e.
```

The measure consequence is only functoriality of pushforward:

```text
map Y eta = map Phi (map X eta).
```

This is a section-image identity.  It says the target p.13 measure is the
raw-order image of the actual p.13 section image measure.  It does not identify
`map X eta` with full raw Haar measure, and it does not attach an
inverse-Jacobian density to a full raw determinant-chart measure.

## Lean Shape

Lean proves:

```text
map_p13RawOrderTuple_eq_map_leftStepRawOrder_image_of_measurable_edgeMatrix
```

Inputs:

- fixed-base edge-matrix measurability, used only to get a.e.-measurability of
  the actual left-step raw tuple;
- an arbitrary source measure `eta`;
- a.e. membership of the actual left-step raw tuple in the raw determinant
  chart.

Conclusion:

```text
Measure.map paperEndpointFixedBaseP13RawOrderTuple eta =
  Measure.map productReductionStepTopologyTupleToChartRawOrder
    (Measure.map p13ProductCoordinateLeftStepRawTopologyTuple eta)
```

The proof derives a.e. measurability of the raw-order map for
`Measure.map X eta` by restricting to the raw determinant chart and using
`Measure.restrict_eq_self_of_ae_mem`.  It derives the required `Ctop`
determinant-unit condition from raw determinant-chart membership, then applies
the existing pointwise p.13 raw-preimage theorem.

## Kill Conditions

- Do not rewrite the right-hand side as full raw Haar or restricted raw Haar.
- Do not add a density conclusion; this theorem is only a pushforward
  functoriality statement for the p.13 section image.
- Do not remove the raw determinant-chart support hypothesis unless a separate
  local determinant-neighborhood/source-support theorem supplies it.
- Do not claim original source coverage, source/prior transport, signed-box
  density identification, normal crossings, pole order, or RLCT.

## Nonclaims

No full raw-Haar pushforward, no product-measure pushforward, no density
transport, no original p.13 source chart, no source coverage, no source/prior
transport, no signed-box density identification, no regular-suspension
certificate, no normal crossings, no pole order, and no RLCT.
