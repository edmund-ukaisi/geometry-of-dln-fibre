# Reproduction - A2 with-following reverse determinant-to-raw domination

Date: 2026-07-02.

## Scope

This note prepares the with-following analogue of the existing Case 2
determinant-to-raw-order measure transport lemma.  It is a source-transport
frontier step, not a chart-piece wrapper.

The target theorem should keep the determinant-side domination hypothesis
explicit:

```text
rawHaar.restrict rawDetChart
  <= c * Measure.map Y (sourceMeasure.restrict V),
```

and prove the raw-order source-side domination:

```text
rawHaar.restrict rawSourceSet
  <= c * Measure.map rawMap (baseJ.restrict V),
```

where:

```text
baseJ = sourceMeasure.withDensity jacobianDensity
jacobianDensity z =
  ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z))
rawMap z = topologyTupleEdgeRawOrder (Y z)
```

Here `Y` is the with-following endpoint topology-tuple map.  The source measure
is arbitrary on the enlarged theta domain, so this does not claim a passive
product/source-prior theorem.

## Pen-and-paper calculation

Let:

```text
Phi y = topologyTupleEdgeRawOrder y
formalDensity y =
  ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt y).
```

On the local determinant sector returned by the with-following source-chart
package, `Y z` lies in the retained-passive determinant chart and:

```text
rawMap z = Phi (Y z).
```

The retained-passive raw-order change-of-variables theorem gives:

```text
Measure.map Phi ((rawHaar.restrict rawDetChart).withDensity formalDensity)
  = rawHaar.restrict rawSourceSet.
```

Assume the determinant-side reverse domination:

```text
rawHaar.restrict rawDetChart
  <= c * Measure.map Y (sourceMeasure.restrict V).
```

Weight both sides by the same determinant-side density `formalDensity`.  This
is valid by monotonicity of `withDensity` under measure domination.  Then push
forward by `Phi`.  The left-hand side becomes `rawHaar.restrict rawSourceSet`
by the retained-passive COV theorem.

The right-hand side becomes:

```text
c * Measure.map Phi
      ((Measure.map Y (sourceMeasure.restrict V)).withDensity formalDensity).
```

Because `Y` is a.e. measurable on `sourceMeasure.restrict V`, the standard
map-with-density identity rewrites this as:

```text
c * Measure.map (fun z => Phi (Y z))
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
rawHaar.restrict rawSourceSet
  <= c * Measure.map rawMap (baseJ.restrict V).
```

## Boundary

This proves only transport of a supplied determinant-side domination through
the retained-passive raw-order COV.  It does not prove:

```text
rawHaar.restrict rawDetChart
  <= c * Measure.map Y (sourceMeasure.restrict V),
```

nor does it identify the source measure with an original DLN source prior,
normalize Haar scalars, prove exact raw-Haar pushforward, prove p.13 coverage,
prove source-rank coverage, construct normal crossings, compute pole order, or
extract RLCT.

## Lean proof plan

Adapt the existing non-following theorem:

```text
exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveTheta_rawMap_baseJ_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple
```

to the enlarged domain
`Case2PassiveThetaWithFollowingFactor`.  The proof should use:

```text
exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_readback_leftInverse
weighted_map_ref_le_smul_map_comp_withDensity_comp_of_le_smul_map
map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_rawSourceChart
restrict_withDensity
```

No source-prior or Haar-transport hypothesis should be hidden in the theorem
statement.
