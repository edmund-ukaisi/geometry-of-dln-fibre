# Reproduction - A2 with-following forward determinant-to-raw domination

Date: 2026-07-02.

## Scope

This note prepares the with-following analogue of the existing Case 2
determinant-to-raw-order forward measure transport lemma.  It is local and
conditional: the determinant-chart domination is supplied as a hypothesis.

The target theorem should assume:

```text
Measure.map Y (sourceMeasure.restrict V)
  <= c * rawHaar.restrict rawDetChart,
```

and prove:

```text
Measure.map rawMap (baseJ.restrict V)
  <= c * rawHaar.restrict rawSourceSet,
```

where:

```text
baseJ = sourceMeasure.withDensity jacobianDensity
jacobianDensity z =
  ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z))
rawMap z = topologyTupleEdgeRawOrder (Y z).
```

As in the reverse theorem, the source measure is arbitrary on the enlarged
with-following theta domain.  No passive-product source prior or Haar transport
is hidden in the statement.

## Pen-and-paper calculation

Let:

```text
Phi y = topologyTupleEdgeRawOrder y
formalDensity y =
  ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt y).
```

On the local determinant sector, the endpoint map satisfies:

```text
Y z in rawDetChart,
rawMap z = Phi (Y z).
```

The retained-passive raw-order change-of-variables theorem gives:

```text
Measure.map Phi ((rawHaar.restrict rawDetChart).withDensity formalDensity)
  = rawHaar.restrict rawSourceSet.
```

Assume:

```text
Measure.map Y (sourceMeasure.restrict V)
  <= c * rawHaar.restrict rawDetChart.
```

Weight both sides by `formalDensity`.  Then push forward by `Phi`.  The
right-hand side becomes `c * rawHaar.restrict rawSourceSet` by the retained
passive COV theorem.  The left-hand side is:

```text
Measure.map Phi
  ((Measure.map Y (sourceMeasure.restrict V)).withDensity formalDensity).
```

Using the map-with-density identity for the a.e. measurable endpoint map `Y`,
this is:

```text
Measure.map (fun z => Phi (Y z))
  ((sourceMeasure.restrict V).withDensity (formalDensity o Y)).
```

Finally:

```text
(sourceMeasure.restrict V).withDensity (formalDensity o Y)
  = (sourceMeasure.withDensity jacobianDensity).restrict V
  = baseJ.restrict V,
```

and `fun z => Phi (Y z)` is definitionally `rawMap`.  Therefore:

```text
Measure.map rawMap (baseJ.restrict V)
  <= c * rawHaar.restrict rawSourceSet.
```

## Boundary

This proves only transport of a supplied determinant-side domination through
the retained-passive raw-order COV.  It does not prove:

```text
Measure.map Y (sourceMeasure.restrict V)
  <= c * rawHaar.restrict rawDetChart,
```

nor does it identify `sourceMeasure` with an original DLN source prior, prove
exact raw-Haar pushforward, prove p.13 coverage, prove source-rank coverage,
construct normal crossings, compute pole order, or extract RLCT.

## Lean proof plan

Adapt the existing non-following theorem:

```text
exists_open_subset_measure_map_case2PassiveTheta_rawMap_baseJ_restrict_le_smul_rawHaar_restrict_rawSource_of_endpointTopologyTuple_restrict_le_smul_detHaar
```

to the enlarged domain
`Case2PassiveThetaWithFollowingFactor`.  The proof should use:

```text
exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_readback_leftInverse
map_comp_withDensity_comp_le_smul_of_map_le_smul_of_weighted_map_ref_eq
map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_rawSourceChart
restrict_withDensity
```

The local theorem should not use the raw-image density wrapper theorem or the
inverse-readback Jacobian theorem.
