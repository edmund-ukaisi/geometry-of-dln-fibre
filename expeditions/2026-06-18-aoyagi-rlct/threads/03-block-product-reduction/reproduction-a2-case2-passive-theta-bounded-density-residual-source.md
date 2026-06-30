# Reproduction - A2 Case 2 passive theta bounded-density residual-source adapter

Date: 2026-06-30.

Status: pen-and-paper check before the theta-specific bounded-density
residual-source Lean adapter.

## Question

The previous theta product-measure slice handled

```text
sourceMeasure = passiveMeasure.prod weightedBox
```

and an arbitrary source measure locally dominated by this passive-product
comparison measure.  The next source-prior-adjacent socket is the bounded
density case:

```text
sourceMeasure = passiveSource.withDensity density,
passiveSource = passiveMeasure.prod weightedBox.
```

What should be required to transfer the residual-source hypotheses?

## Calculation

Let `V` be the local punctured determinant-sector neighborhood returned by the
chart-produced residual-source socket.  If the density is locally bounded on
that sector,

```text
forall^ae z in passiveSource.restrict V,
  density z <= c,
c < infinity,
```

then the restricted weighted source measure is dominated by a finite scalar
multiple of the passive-product comparison measure:

```text
(passiveSource.withDensity density).restrict V
  <= c • passiveSource.
```

This is the measure-theoretic lemma already formalized as
`restrict_withDensity_le_smul_of_ae_le`.

Mapping by the selected residual readout gives domination of the restricted
`yNext` marginal, and the selected-entry signed-box theorem supplies residual
positivity and finite negative-power integrability for `weightedBox` under

```text
0 <= t,
forall i, 0 < Rres i,
2*t < card(center.erase (J+2,J+2)) + 1.
```

Together with finite passive mass, this discharges the retained-passive
residual-source conclusion for

```text
mu = Measure.map sourceChart
  ((passiveSource.withDensity density).restrict V).
```

The result should expose the local bounded-density hypothesis after `V` is
chosen, because `V` is produced by the chart theorem and is not predetermined
by the density.

## Intended Lean Shape

Specialize the generic theorem

```text
exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_of_withDensity_ae_le_const_passiveProductMeasure_finiteMass
```

with

```text
eta = Case2PassiveTheta.PassiveFields.
```

The concrete theta theorem should take

```text
sourceDensity : Case2PassiveTheta ... -> ENNReal
passiveMeasure : Measure Case2PassiveTheta.PassiveFields
passiveMeasure Set.univ < infinity
```

and return `V` such that, for

```text
passiveSource = passiveMeasure.prod weightedBox,
sourceMeasure = passiveSource.withDensity sourceDensity,
mu = Measure.map sourceChart (sourceMeasure.restrict V),
```

we have retained-passive local-source support and, for every finite `c`, the
local a.e. bound

```text
forall^ae z in passiveSource.restrict V,
  sourceDensity z <= c
```

implies residual positivity and `residualNegPowerIntegrableOn localSource mu t`.

## Source Boundary

Aoyagi pp. 10-13 support the retained-passive p.13 coordinate/source chart, and
pp. 19-22 support the Case 2 selected-entry residual calculation.  The present
step is measure bookkeeping over previously formalized selected-entry
signed-box estimates and chart-produced source-readback facts.  It uses no
quiver-paper evidence and no new cited theorem.

## Nonclaims

This slice does not construct the density from the original source prior, prove
that the original source prior satisfies the local bound, prove exact
restricted `yNext` marginal equality, determinant-chart Haar transport,
raw-order Haar transport, source-prior transport, exact passive-sector
pushforward, source-image equality, source-rank coverage, normal crossings,
pole order, or RLCT extraction.

