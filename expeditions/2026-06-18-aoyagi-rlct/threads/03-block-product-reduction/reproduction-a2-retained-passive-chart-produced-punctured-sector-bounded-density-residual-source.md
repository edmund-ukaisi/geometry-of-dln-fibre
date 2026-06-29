# A2 retained-passive chart-produced punctured-sector bounded-density residual source

## Scope

This note reproduces the next small source-measure bridge after the local
domination socket.  It still does not prove an external/original DLN source
prior comparison.  It proves the conditional statement that if a proposed
source measure is supplied as a locally bounded density with respect to the
passive-product selected-entry coordinate measure, then it satisfies the
local domination hypothesis required by the socket.

The previous theorem exposed the needed condition directly:

```text
sourceMeasure.restrict V <= c • passiveSource.
```

The present target specializes

```text
sourceMeasure = passiveSource.withDensity sourceDensity
```

and replaces the domination field by the local density bound

```text
forall a.e. z with respect to passiveSource.restrict V,
  sourceDensity z <= c.
```

Here `c : ENNReal` is finite in the residual-source conclusion.

## Objects

Use the same passive Case 2 selected-entry coordinate domain as the banked
local-domination theorem:

```text
center = case2ResidualBlockPivotEntries n S (J + 1),
pivotNext = (J + 2, J + 2) in center,
X = eta x (center -> R).
```

For positive radii `Rres`, let

```text
signedBox =
  Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),

weightedBox =
  signedBox.withDensity
    (fun y : center -> R =>
      ENNReal.ofReal
        (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y)),

passiveSource = passiveMeasure.prod weightedBox.
```

Let

```text
sourceDensity : X -> ENNReal,
sourceMeasure = passiveSource.withDensity sourceDensity.
```

The socket chooses an open determinant-and-pivot-nonzero sector `V` around
`z0`.  The new conditional field should be:

```text
forall {c : ENNReal},
  c < infinity ->
  (forall a.e. z with respect to passiveSource.restrict V,
    sourceDensity z <= c) ->
  residual-source conclusion for
    mu = Measure.map sourceChart ((passiveSource.withDensity sourceDensity).restrict V).
```

The support equality `mu.restrict localSource = mu` is still unconditional,
because it comes from the punctured-sector support/readout socket rather than
from the density bound.

## Measure calculation

The generic measure-theory lemma is:

```text
if hs : MeasurableSet s
and hf : forall a.e. x with respect to mu.restrict s, f x <= c,
then
  (mu.withDensity f).restrict s <= c • mu.
```

Proof:

1. Since `s` is measurable,

```text
(mu.withDensity f).restrict s = (mu.restrict s).withDensity f.
```

2. The a.e. bound gives by `withDensity_mono`

```text
(mu.restrict s).withDensity f
  <= (mu.restrict s).withDensity (fun _ => c).
```

3. The constant-density identity rewrites the right hand side as

```text
c • mu.restrict s.
```

4. Since `mu.restrict s <= mu`, scalar monotonicity gives

```text
c • mu.restrict s <= c • mu.
```

The existing helper `measure_le_smul_of_le_smul_restrict` already packages
the last step.

Apply this lemma with

```text
mu = passiveSource,
f = sourceDensity,
s = V.
```

The sector `V` is open, hence measurable, so the helper gives exactly

```text
(passiveSource.withDensity sourceDensity).restrict V
  <= c • passiveSource.
```

This discharges the local-domination field in the banked theorem

```text
exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_of_restrict_le_smul_passiveProductMeasure_finiteMass.
```

## Kill conditions

- Kill if the theorem claims that an external/original source prior has the
  supplied density.  The density and local bound are explicit inputs.
- Kill if the density bound is stated globally when the proof only needs the
  bound on `passiveSource.restrict V`.
- Kill if scalar finiteness `c < infinity` is omitted from the residual-source
  conclusion.
- Kill if the theorem is described as determinant-chart Haar transport,
  raw/source Haar transport, original source-prior transport, passive
  Jacobian transport, source-image equality, source-rank coverage, normal
  crossings, pole order, or RLCT.

## Formalisation target

Add a reusable helper to:

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
```

Suggested name:

```text
restrict_withDensity_le_smul_of_ae_le
```

Add the Aoyagi wrapper to:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean
```

Suggested theorem name:

```text
exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_of_withDensity_ae_le_const_passiveProductMeasure_finiteMass
```

The theorem should return the same open sector `V` as the local-domination
wrapper and replace its local domination assumption by the a.e. density bound
on `passiveSource.restrict V`.
