# Reproduction - A2 Case 2 Passive Selected-Entry Weighted Local Source Support After Open Restriction

Date: 2026-06-29.

Status: controller reproduction before Lean formalisation.  This is
measure-support bookkeeping after weighting the already restricted passive
selected-entry coordinate-domain measure.  It is not a Jacobian formula or
source-prior transport theorem.

## Source Slice

Aoyagi pp. 10-13 motivate the retained-passive p.13 source variables and the
determinant-chart substitutions.  The local source-readback theorem gives the
coordinate-side fact needed here: from passive-field continuity and
determinant-unit hypotheses at one base point, there is an open determinant
domain `U` such that every passive selected-entry source chart point over `U`
lies in the retained-passive p.13 local source.

The previous restricted-support theorem turned this pointwise statement into
support of

```text
Measure.map sourceChart (sourceMeasure.restrict U).
```

The present note records the same support after replacing the restricted
domain measure by an arbitrary `withDensity` weighting.

## Measure Calculation

Let `density : domain -> ENNReal`, where

```text
domain = eta x (center -> R).
```

Define

```text
base     = sourceMeasure.restrict U
weighted = base.withDensity density.
```

Mathlib's basic `withDensity` theorem gives

```text
weighted << base.
```

The open-domain source theorem supplies

```text
forall^ae z in base, sourceChart z in localSource.
```

Absolute continuity transfers this to the weighted measure:

```text
forall^ae z in weighted, sourceChart z in localSource.
```

The same local determinant-domain argument gives

```text
AEMeasurable sourceChart base.
```

Again, absolute continuity transfers a.e. measurability:

```text
AEMeasurable sourceChart weighted.
```

The generic retained-passive support helper then applies with
`eta := weighted`:

```text
(Measure.map sourceChart weighted).restrict localSource
  =
Measure.map sourceChart weighted.
```

No measurability, positivity, boundedness, or nonvanishing assumption on
`density` is needed for this support statement.

## Lean Target

The theorem should be the arbitrary-density analogue of the existing
restricted support theorem:

```text
exists_open_measure_map_case2EndpointTransport_withPassive_withDensity_restrict_retainedPassiveP13LocalSource_eq_self
```

It should assume:

- continuity of `A1passive`, `F2`, `A3passive`, `Ctop`, and `F3`;
- determinant-unit hypotheses only at the base point `z0`;
- an arbitrary source-domain measure `sourceMeasure`;
- an arbitrary density on the passive selected-entry coordinate domain;
- Borel/measurable-space structure on the source edge-family type, used to
  state and derive a.e. measurability.

It should prove:

- `IsOpen U`;
- `z0 in U`;
- pointwise local-source membership and readback equality for every `z in U`;
- support of

```text
Measure.map sourceChart ((sourceMeasure.restrict U).withDensity density)
```

on `localSource`.

## Nonclaims

This theorem does not prove that `density` is a Jacobian, does not compare an
original source prior with a chart-domain measure, and does not prove
determinant-chart Haar pushforward, raw/source Haar transport, selected-entry
source-image equality, local coverage, source-rank support or coverage, exact
localized residual marginal, normal crossings, pole order, or RLCT extraction.
