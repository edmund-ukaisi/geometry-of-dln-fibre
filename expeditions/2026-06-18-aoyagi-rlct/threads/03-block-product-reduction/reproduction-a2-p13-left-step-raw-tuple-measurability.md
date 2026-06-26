# Reproduction - A2 p.13 left-step raw tuple measurability

Date: 2026-06-26.

Status: Lean proved; xhigh review passed.

## Question

The conditional p.13 left-step raw pushforward consumer previously needed the
actual raw source tuple to be a.e.-measurable.  This is finite Borel
bookkeeping, not a source theorem: once the fixed-base edge matrices are
measurable, the deterministic suffix recursion and the p.13 regular
coordinates should make the raw tuple measurable.

The target is to remove only this measurability input.  The source/product-chart
raw pushforward

```text
Measure.map p13ProductCoordinateLeftStepRawTopologyTuple eta =
  m.restrict rawDetChart
```

must remain an explicit hypothesis.

## Pen-and-Paper Check

Let

```text
E_p(x)
```

be the fixed-basis reversed edge matrix family used by the suffix recursion.
Assume the Pi-valued family `x |-> (p |-> E_p(x))` is measurable.  The suffix
state is built from finite real matrices by block projection, block assembly,
addition, negation, multiplication, subtraction, and total matrix inverse.  As
in the earlier residual-coordinate measurability slice, total matrix inverse is
Borel measurable over `R`; no determinant-chart assumption is needed.

Therefore the suffix recursion gives measurable fields for the relevant state.
In particular the tail residual product

```text
Dtail(x)
```

and the left residual block

```text
C0(x)
```

are measurable functions of the fixed-base edge matrices.

The p.13 raw source tuple is

```text
X(x,u) = (I,Dtail(x),F3(u),Ctop(u),-Ctop(u)*F2(u),0,C0(x)).
```

The remaining entries are either constant or finite matrix-coordinate
projections from the Euclidean regular-coordinate variable `u`; multiplication
and negation preserve measurability.  Hence `X` is measurable, and therefore
a.e.-measurable for every source measure `eta`.

The actual constructed left-step raw tuple has already been proved equal to
this explicit raw preimage tuple:

```text
p13ProductCoordinateLeftStepRawTopologyTuple_eq_rawPreimageTuple.
```

Thus the actual raw tuple is measurable under the same fixed-base edge-matrix
measurability hypothesis.

## Lean Shape

`ChartTopology.lean` adds the two suffix-recursion projections needed by the
p.13 tuple:

```text
measurable_chartLocalSuffixState_residualProduct_real
measurable_chartLocalSuffixState_residualBlock_real
```

`ProductReductionStepRegularDensity.lean` then proves:

```text
measurable_paperEndpointFixedBaseP13RawPreimageTuple_of_measurable_edgeMatrix
aemeasurable_paperEndpointFixedBaseP13RawPreimageTuple_of_measurable_edgeMatrix
measurable_p13ProductCoordinateLeftStepRawTopologyTuple_of_measurable_edgeMatrix
aemeasurable_p13ProductCoordinateLeftStepRawTopologyTuple_of_measurable_edgeMatrix
```

Finally the conditional measure consumer gets a convenience wrapper:

```text
map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_leftStepRaw_map_of_measurable_edgeMatrix
```

This theorem takes fixed-base edge-matrix measurability and the same explicit
raw pushforward hypothesis as before.  It derives the a.e.-measurability input
for `p13ProductCoordinateLeftStepRawTopologyTuple` and calls the earlier
conditional raw pushforward consumer.

## Kill Conditions

- Do not claim the raw pushforward from edge-matrix measurability.  The new
  theorem still assumes the raw pushforward.
- Do not add a determinant-chart or `det(Ctop)` hypothesis for raw-tuple
  measurability.  Those belong to support/pointwise chart identities, not to
  finite Borel measurability.
- Do not replace fixed-base edge-matrix measurability by raw `Measurable
  CedgeBase` unless the continuous-linear-map measurable structure has been
  explicitly supplied.
- Do not use this as a source coverage, signed-box density, original prior
  transport, normal-crossing, pole-order, or RLCT theorem.

## Nonclaims

No proof of the supplied raw pushforward, no original p.13 source chart, no
source coverage, no original DLN source/prior transport, no signed-box density
identification, no product-measure pushforward, no regular-suspension
certificate, no normal crossings, no pole order, and no RLCT.
