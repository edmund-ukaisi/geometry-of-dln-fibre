# Reproduction - A2 Case 2 passive theta global Jacobian-weighted single open

Date: 2026-06-30.

Status: pen-and-paper check before Lean.  This is a repackaging of the
Jacobian-weighted residual-source theorem, not a new transport theorem.

## Question

The previous Jacobian-weighted residual-source theorem builds the theta source
measure as

```text
((passiveSource.restrict U).withDensity jacobianDensity).restrict V.
```

Can we state the same result for the globally weighted theta measure

```text
passiveSource.withDensity jacobianDensity
```

restricted once to a single open neighborhood?

Answer: yes.  Take the single open neighborhood to be `W = U ∩ V`.  The proof
is only the commutation of restriction with `withDensity`.

## Calculation

Let

```text
passiveSource = passiveMeasure.prod weightedBox,
Y z = case2PassiveThetaEndpointTopologyTuple z,
J z = retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z),
jacobianDensity z = ofReal (J z).
```

The already proved theorem returns open neighborhoods `U` and `V` such that the
mapped measure

```text
Measure.map sourceChart
  (((passiveSource.restrict U).withDensity jacobianDensity).restrict V)
```

satisfies retained-passive local-source support, a.e. residual square-sum
positivity, and `residualNegPowerIntegrableOn`.

Since `U` and `V` are open, they are measurable.  Hence

```text
(passiveSource.withDensity jacobianDensity).restrict (U ∩ V)
  = (passiveSource.restrict (U ∩ V)).withDensity jacobianDensity
```

by `restrict_withDensity`, while

```text
((passiveSource.restrict U).withDensity jacobianDensity).restrict V
  = ((passiveSource.restrict U).restrict V).withDensity jacobianDensity
  = (passiveSource.restrict (V ∩ U)).withDensity jacobianDensity
```

again by `restrict_withDensity` and by repeated restriction.  Commuting the
intersection gives equality with the global-weighted restricted measure over
`U ∩ V`.

Therefore the old conclusion transfers definitionally after rewriting the
measure under `Measure.map sourceChart`.

## Intended Lean Shape

Add a theorem to

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean
```

with public name:

```text
exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_passiveProductMeasure_globalWithDensity_jacobian_finiteMass
```

It should call

```text
exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_passiveProductMeasure_withDensity_jacobian_finiteMass
```

and return `W = U ∩ V`.

## Source Boundary

Aoyagi pp. 10-13 support the retained-passive p.13 coordinate chart and
Jacobian-unit interpretation; pp. 19-22 support the Case 2 selected-entry
residual calculation used by the residual-source handoff.  This step is a
measure-form repackaging of already formalized local bookkeeping.  It uses no
quiver-paper evidence and no new cited theorem.

## Nonclaims

This slice does not prove determinant-chart Haar transport, raw-order Haar
transport, source-prior transport, exact passive-sector pushforward,
source-image equality, source-rank coverage, construction of an original
source-prior density, normal crossings, pole order, or RLCT extraction.
