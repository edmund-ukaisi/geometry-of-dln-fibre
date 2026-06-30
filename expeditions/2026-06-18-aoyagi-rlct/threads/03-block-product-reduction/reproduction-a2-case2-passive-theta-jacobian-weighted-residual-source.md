# Reproduction - A2 Case 2 passive theta Jacobian-weighted residual source

Date: 2026-06-30.

Status: pen-and-paper check before Lean.  This is a local domination
composition, not a determinant-chart Haar or source-prior transport theorem.

## Question

The theta Jacobian sandwich proves that, near a passive determinant-sector base
point, weighting the passive-product theta measure by the retained-passive
raw-order Jacobian factor changes the measure only by bounded constants.  Can
we feed this Jacobian-weighted local theta measure into the retained-passive
residual-source socket?

Answer: yes, by domination.  No exact pushforward or source-prior theorem is
needed.

## Setup

Let

```text
passiveSource = passiveMeasure.prod weightedBox,
Y z = case2PassiveThetaEndpointTopologyTuple z,
J z = retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z).
```

At a base point `z0` in the passive determinant sector with nonzero selected
pivot, the theta Jacobian sandwich gives positive constants `epsilon`, `K`
and an open neighborhood `U` of `z0` such that

```text
(passiveSource.restrict U).withDensity (fun z => ofReal (J z))
  <= ofReal K • passiveSource.restrict U.
```

Since restriction is monotone,

```text
passiveSource.restrict U <= passiveSource,
```

so the same Jacobian-weighted measure is dominated globally by the unweighted
comparison measure:

```text
(passiveSource.restrict U).withDensity (fun z => ofReal (J z))
  <= ofReal K • passiveSource.
```

The scalar `ofReal K` is finite.

## Residual-Source Handoff

Apply the existing theta local-domination theorem to the arbitrary source
measure

```text
sourceMeasure =
  (passiveSource.restrict U).withDensity (fun z => ofReal (J z)).
```

That theorem returns an open punctured determinant-sector neighborhood `V` of
`z0` such that, for

```text
mu = Measure.map sourceChart (sourceMeasure.restrict V),
```

the chart-produced measure is supported on the retained-passive p.13 local
source.  Its residual-source conclusion is conditional on

```text
sourceMeasure.restrict V <= c • passiveSource,
c < infinity.
```

Taking `c = ofReal K` discharges the condition because

```text
sourceMeasure.restrict V <= sourceMeasure <= ofReal K • passiveSource.
```

Thus the Jacobian-weighted local theta source measure has a.e. residual
square-sum positivity and finite negative-power integrability after the
chart-produced source pushforward.

## Intended Lean Shape

Add a second theorem to

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean
```

with public name:

```text
exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_passiveProductMeasure_withDensity_jacobian_finiteMass
```

It should combine:

```text
exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2PassiveThetaEndpointTopologyTuple_passiveProductMeasure
exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_restrict_le_smul_passiveProductMeasure_finiteMass
```

and use `measure_le_smul_of_le_smul_restrict` plus restriction monotonicity to
provide the local domination input.

## Source Boundary

Aoyagi pp. 10-13 support the retained-passive p.13 coordinate chart and
Jacobian-unit interpretation; pp. 19-22 support the Case 2 selected-entry
residual calculation used by the residual-source handoff.  The present step is
measure bookkeeping over already formalized chart/Jacobian and selected-entry
estimates.  It uses no quiver-paper evidence and no new cited theorem.

## Nonclaims

This slice does not prove determinant-chart Haar transport, raw-order Haar
transport, source-prior transport, exact passive-sector pushforward,
source-image equality, source-rank coverage, construction of an original
source-prior density, normal crossings, pole order, or RLCT extraction.
