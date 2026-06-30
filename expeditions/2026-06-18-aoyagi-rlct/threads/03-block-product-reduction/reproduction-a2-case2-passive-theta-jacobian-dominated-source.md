# Reproduction - A2 Case 2 passive theta Jacobian-dominated source

Date: 2026-06-30.

Status: pen-and-paper check before Lean.  This is a local domination socket
over the globally Jacobian-weighted passive theta measure, not a source-prior
construction.

## Question

Suppose a candidate theta-domain source measure is locally dominated by the
globally Jacobian-weighted passive-product theta measure

```text
baseJ = passiveSource.withDensity jacobianDensity.
```

Can the existing passive-product residual-source theorem be reused to prove
retained-passive local-source support, a.e. residual square-sum positivity, and
`residualNegPowerIntegrableOn` for the candidate source after shrinking to a
punctured determinant-sector neighborhood?

Answer: yes.  The local upper bound on the Jacobian density converts
domination by `baseJ` into domination by the unweighted passive product source,
which is exactly the existing residual-source socket.

## Setup

Let

```text
passiveSource = passiveMeasure.prod weightedBox,
Y z = case2PassiveThetaEndpointTopologyTuple z,
J z = retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z),
jacobianDensity z = ofReal (J z),
baseJ = passiveSource.withDensity jacobianDensity.
```

The theta base point `z0` lies in the passive determinant sector and has
nonzero selected pivot.  The selected-entry radii are positive, `0 <= t`, and
the selected-entry critical inequality holds.

The existing Jacobian sandwich gives positive constants `epsilon`, `K` and an
open neighborhood `U` of `z0` such that

```text
(passiveSource.restrict U).withDensity jacobianDensity
  <= ofReal K * passiveSource.restrict U.
```

The existing arbitrary-source passive-product residual-source theorem is then
applied to

```text
restrictedCandidate = candidateMeasure.restrict U.
```

It returns an open punctured sector `V` of `z0`.  The final open set is

```text
W = U inter V.
```

## Domination Calculation

Assume that, for some finite scalar `c`,

```text
candidateMeasure.restrict W <= c * baseJ.restrict W.
```

Because `U` and `V` are open, they are measurable, and repeated restriction
gives

```text
(candidateMeasure.restrict U).restrict V
  = candidateMeasure.restrict (U inter V).
```

Also, `restrict_withDensity` gives

```text
baseJ.restrict (U inter V)
  = ((passiveSource.restrict U).withDensity jacobianDensity).restrict V.
```

Thus the local domination hypothesis rewrites to

```text
(candidateMeasure.restrict U).restrict V
  <= c * (((passiveSource.restrict U).withDensity jacobianDensity).restrict V).
```

The Jacobian upper bound and restriction monotonicity give

```text
(((passiveSource.restrict U).withDensity jacobianDensity).restrict V)
  <= ofReal K * passiveSource.
```

Therefore

```text
(candidateMeasure.restrict U).restrict V
  <= (c * ofReal K) * passiveSource.
```

Since `c < infinity` and `ofReal K < infinity`, the product scalar is finite.
This is the exact hypothesis expected by the arbitrary-source
passive-product residual-source theorem.

## Lean Target

Add a theorem to

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean
```

with public name:

```text
exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_restrict_le_smul_globalWithDensity_jacobian_passiveProductMeasure_finiteMass
```

The theorem returns `W = U inter V`.  For the chart-produced measure

```text
mu = Measure.map sourceChart (candidateMeasure.restrict W)
```

it proves local-source support unconditionally, and proves residual positivity
plus `residualNegPowerIntegrableOn localSource mu t` under the explicit local
finite-scalar domination by `baseJ.restrict W`.

## Source Boundary

Aoyagi pp. 10-13 support the retained-passive p.13 coordinate algebra and the
Jacobian-unit interpretation already formalized in the theta Jacobian sandwich.
Aoyagi pp. 19-22 support the selected-entry Case 2 residual calculation already
used by the residual-source handoff.  This step adds no new source claim: it is
measure-domination bookkeeping over existing formalized Aoyagi algebra.

## Nonclaims

This slice does not construct an original source prior, identify
determinant-chart Haar measure, prove raw-order Haar transport, prove an exact
passive-sector pushforward, prove source-image equality or source-rank
coverage, construct normal crossings, compute pole order, or extract RLCT.
