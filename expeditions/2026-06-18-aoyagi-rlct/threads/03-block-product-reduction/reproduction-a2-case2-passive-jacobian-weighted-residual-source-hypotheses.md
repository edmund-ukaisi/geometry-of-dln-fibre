# Reproduction - A2 Case 2 Passive Jacobian-Weighted Residual Source Hypotheses

Date: 2026-06-29.

Status: controller pen-and-paper reproduction before Lean banking.  This is a
packaging theorem for the residual-source socket.  It does not add a new
Jacobian formula or identify an external source prior.

## Question

The banked passive Jacobian-weighted residual theorem gives an open
neighborhood `U` of `z0` and, for

```text
weighted =
  (sourceMeasure.restrict U).withDensity (fun z => ofReal (J z))

muJ = Measure.map sourceChart weighted,
```

proves

```text
for muJ-a.e. E,
  0 < aoyagiCoordinateSquareSum (residualMap_center E)

int^- E,
  ofReal ((aoyagiCoordinateSquareSum (residualMap_center E))^(-t)) d muJ
  < infinity.
```

Here `residualMap_center` is the residual block coordinate family reindexed by
the selected-entry coordinate set `center`.

The residual-source consumers expect the same statement over the retained
passive p.13 local source:

```text
for muJ.restrict localSource-a.e. E,
  0 < aoyagiCoordinateSquareSum (residualMap_source E)

residualNegPowerIntegrableOn ... localSource muJ t.
```

Can this be proved without changing the measure or adding a new analytic
input?  Yes.

## Calculation

Let

```text
residualMap_source E =
  paperEndpointFixedBaseResidualBlockCoordinateMap ... E
```

with its native fixed-base residual-coordinate index.  Let

```text
residualCoordEquiv : source residual-coordinate index ~= center
```

be the Case 2 selected-entry residual-coordinate equivalence, and define

```text
residualMap_center E c =
  residualMap_source E (residualCoordEquiv.symm c).
```

Reindexing a finite coordinate family does not change its square sum:

```text
aoyagiCoordinateSquareSum (residualMap_center E)
  =
aoyagiCoordinateSquareSum (residualMap_source E).
```

This is exactly `aoyagiCoordinateSquareSum_comp_equiv` applied to
`residualCoordEquiv.symm`.  Therefore the already proved positivity and
finite integral for `residualMap_center` are the corresponding positivity and
finite integral for `residualMap_source`.

It remains only to pass from `muJ` to `muJ.restrict localSource`.  The
chart-produced source family lies in the retained-passive p.13 local source
for every source-domain point.  Since `sourceChart` is measurable on the
weighted restricted domain, the general support lemma gives

```text
muJ.restrict localSource = muJ.
```

Rewriting by this equality transfers the almost-everywhere positivity and
turns the whole-measure finite integral into

```text
residualNegPowerIntegrableOn ... localSource muJ t,
```

because `residualNegPowerIntegrableOn` is the same negative-power lintegral
against `muJ.restrict localSource`.

## Lean Targets

Use the banked whole-measure theorem:

```text
exists_open_residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass
```

and package it as:

```text
exists_open_residualSourceHypotheses_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass
```

The support equality should use:

```text
measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_restrict_retainedPassiveP13LocalSource_eq_self
```

with `sourceMeasure := weighted`.

## Dependency Boundary

The theorem uses only:

- the already proved Jacobian-weighted domination residual theorem;
- reindexing invariance of finite coordinate square sums;
- chart-produced support on the retained-passive local source.

It does not use a determinant-chart Haar theorem, raw/source Haar theorem,
source-prior theorem, source-image coverage theorem, normal-crossing
presentation, pole-order computation, or RLCT extraction.

## Nonclaims

- No exact localized residual marginal.
- No determinant-chart Haar pushforward.
- No raw/source Haar theorem.
- No original or external DLN source prior.
- No source-prior Jacobian formula.
- No source-image equality or local coverage.
- No normal crossings, pole order, or RLCT.
