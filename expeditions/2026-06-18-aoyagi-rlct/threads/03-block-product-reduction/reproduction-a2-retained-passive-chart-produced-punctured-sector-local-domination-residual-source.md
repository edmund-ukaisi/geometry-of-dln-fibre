# A2 retained-passive chart-produced punctured-sector local-domination residual source

## Scope

This note reproduces a generic measure-theory wrapper around the
punctured-sector residual-source socket.  It does not add a new Aoyagi
coordinate calculation.  It also does not prove an external/original source
prior comparison.  Instead, it records the exact local pullback domination
condition that would be sufficient to use the passive-product selected-entry
residual calculation for an arbitrary coordinate-domain source measure.

The previous passive-product theorem handled the special case

```text
sourceMeasure = passiveMeasure.prod weightedBox.
```

The present target keeps `sourceMeasure` arbitrary.  After the socket chooses
the open punctured sector `V`, assume

```text
sourceMeasure.restrict V <= c • (passiveMeasure.prod weightedBox)
```

for some finite scalar `c`.  Then the same residual-source conclusion follows.

## Objects

Keep the same Case 2 passive selected-entry data as in the preceding
punctured-sector cards.  Let

```text
center = case2ResidualBlockPivotEntries n S (J + 1),
pivotNext = (J + 2, J + 2) in center,
X = eta x (center -> R).
```

For radii `Rres : center -> R` with `0 < Rres i`, define

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

Assume

```text
passiveMeasure Set.univ < infinity,
0 <= t,
2 * t < card(center.erase pivotNext.1) + 1,
0 < Rres i for all i.
```

Let `sourceMeasure : Measure X` be arbitrary.  The residual-source socket gives
an open determinant-and-pivot-nonzero sector `V`, with `z0 in V`, and defines

```text
mu = Measure.map sourceChart (sourceMeasure.restrict V),
marginal = Measure.map Prod.snd (sourceMeasure.restrict V).
```

The target theorem should expose the local domination field after `V` exists:

```text
forall c, c < infinity ->
  sourceMeasure.restrict V <= c • passiveSource ->
    mu.restrict localSource = mu
    and residual positivity/integrability for mu.
```

The support equality `mu.restrict localSource = mu` actually comes from the
socket and does not depend on the domination assumption.  It is still packaged
with the residual conclusion for downstream convenience.

## First marginal: passive product

The product marginal of the passive source is

```text
Measure.map Prod.snd passiveSource
  = passiveMeasure Set.univ • weightedBox.
```

This is equality by `Measure.map_snd_prod`.  The raw selected-entry theorem
gives residual positivity and finite negative-power integral over
`weightedBox`.  Rewriting by the equality above:

```text
Measure.map Prod.snd passiveSource <= passiveMeasure Set.univ • weightedBox,
```

the helper `ae_of_measure_le_smul` transfers positivity from `weightedBox` to
`Measure.map Prod.snd passiveSource`.  Since `passiveMeasure Set.univ <
infinity`, the helper `lintegral_lt_top_of_measure_le_smul` transfers the
finite lower integral to the same passive product marginal.

This step is the same as in the concrete passive-product theorem, except it is
kept as an intermediate marginal rather than immediately using the passive
source itself.

## Second marginal: arbitrary source dominated locally

Assume after the sector is chosen that

```text
hsource_le : sourceMeasure.restrict V <= c • passiveSource,
hc : c < infinity.
```

Mapping by the measurable projection `Prod.snd` preserves scalar domination:

```text
Measure.map Prod.snd (sourceMeasure.restrict V)
  <= c • Measure.map Prod.snd passiveSource.
```

This is exactly `map_le_smul_map_of_le_smul measurable_snd hsource_le`.

The first-marginal positivity and finite-integral facts then transfer once more
to

```text
marginal = Measure.map Prod.snd (sourceMeasure.restrict V)
```

using `ae_of_measure_le_smul` and `lintegral_lt_top_of_measure_le_smul` with
the scalar `c`.

## Socket application

The socket requires two marginal hypotheses:

```text
marginal-a.e. y, 0 < SelectedEntrySignedBox.CenterCoord.residual pivotNext y,

integral over marginal of
  ENNReal.ofReal ((SelectedEntrySignedBox.CenterCoord.residual pivotNext y)^(-t))
is finite.
```

The two-step domination transfer supplies both.  Feeding them to

```text
exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_marginal
```

proves the retained-passive residual-source hypotheses for

```text
mu = Measure.map sourceChart (sourceMeasure.restrict V).
```

## Kill conditions

- Kill if the theorem claims to prove the domination assumption for an external
  source prior.  The domination is an explicit input.
- Kill if it uses equality of `sourceMeasure.restrict V` with the passive
  product measure, or equality of restricted residual marginals.  Only
  domination is used.
- Kill if scalar finiteness is omitted for the finite-integral transfers:
  both `passiveMeasure Set.univ < infinity` and `c < infinity` are needed.
- Kill if the theorem is named or described as determinant-chart Haar
  transport, raw/source Haar transport, original source-prior transport, a
  passive Jacobian formula, source-image equality, source-rank coverage,
  normal crossings, pole order, or RLCT.

## Formalisation target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean
```

Target theorem:

```text
exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_of_restrict_le_smul_passiveProductMeasure_finiteMass
```

The theorem should return the open punctured sector `V` and a conditional
residual-source conclusion under the explicit local domination hypothesis
`sourceMeasure.restrict V <= c • passiveSource` with `c < infinity`.
