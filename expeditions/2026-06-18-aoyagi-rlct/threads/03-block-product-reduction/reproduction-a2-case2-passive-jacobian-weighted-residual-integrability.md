# Reproduction - A2 Case 2 Passive Jacobian-Weighted Residual Integrability

Date: 2026-06-29.

Status: controller pen-and-paper reproduction before Lean banking.  This is a
local domination handoff for the Jacobian-weighted restricted passive-domain
measure.  It is not a localized residual-marginal equality.

## Question

The passive Jacobian sandwich gives an open neighborhood `U` of `z0` and
positive constants `epsilon`, `K` such that

```text
(sourceMeasure.restrict U).withDensity (fun z => ofReal (J z))
  <= ofReal K • sourceMeasure.restrict U.
```

The passive finite-mass residual theorem gives residual positivity and finite
negative-power integral for

```text
muBase = Measure.map sourceChart sourceMeasure.
```

Can these facts be transferred to the local Jacobian-weighted measure

```text
muJ =
  Measure.map sourceChart
    ((sourceMeasure.restrict U).withDensity (fun z => ofReal (J z)))?
```

Answer: yes, by measure domination.  The upper half of the Jacobian sandwich
dominates the weighted restricted measure by a finite scalar multiple of the
global passive product-domain measure; mapping by the source chart preserves
that domination.  The passive finite-mass residual theorem then transfers
through absolute continuity and lower-integral monotonicity.

## Calculation

Write

```text
weighted =
  (sourceMeasure.restrict U).withDensity (fun z => ofReal (J z)).
```

The upper sandwich gives

```text
weighted <= ofReal K • sourceMeasure.restrict U.
```

Since restriction is monotone,

```text
sourceMeasure.restrict U <= sourceMeasure,
```

hence

```text
weighted <= ofReal K • sourceMeasure.
```

Mapping by a measurable `sourceChart` preserves domination by a scalar
multiple:

```text
Measure.map sourceChart weighted
  <= ofReal K • Measure.map sourceChart sourceMeasure.
```

Let

```text
muJ    = Measure.map sourceChart weighted
muBase = Measure.map sourceChart sourceMeasure.
```

The already proved passive finite-mass theorem gives

```text
for muBase-a.e. E,
  0 < aoyagiCoordinateSquareSum (residualMap E)

int^- E,
  ofReal ((aoyagiCoordinateSquareSum (residualMap E))^(-t)) d muBase
  < infinity.
```

Because `muJ <= ofReal K • muBase`, `muJ` is absolutely continuous with respect
to `muBase`.  Therefore the a.e. positivity statement transfers from `muBase`
to `muJ`.

For the integral, monotonicity in the measure gives

```text
int^- E, f E d muJ
  <= int^- E, f E d (ofReal K • muBase).
```

The scalar integral identity rewrites the right side as

```text
ofReal K * int^- E, f E d muBase,
```

which is finite because `ofReal K < infinity` and the base integral is finite.

## Lean Targets

Reusable measure-domination helpers:

```text
ae_of_measure_le_smul
lintegral_lt_top_of_measure_le_smul
map_le_smul_map_of_le_smul
measure_le_smul_of_le_smul_restrict
```

Case 2 passive theorem:

```text
exists_open_residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass
```

## Dependency Boundary

This proof uses only the local Jacobian upper sandwich and the global passive
finite-mass residual theorem.  The lower sandwich is available but not needed
for this integrability handoff.  The finite total passive mass hypothesis
remains necessary because it is inherited from the base residual theorem.

## Nonclaims

- No exact localized residual marginal.
- No determinant-chart Haar pushforward.
- No raw/source Haar theorem.
- No original or external DLN source prior.
- No source-prior Jacobian formula.
- No source-image equality or coverage.
- No local inverse or coverage theorem.
- No normal crossings, pole order, or RLCT.
