# Statement card: A2 retained-passive local formal/product-density COV

## Lean target

New file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalJacobianMeasure.lean
```

Additional wrappers in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobianMeasure.lean
```

## New names

Coordinate-level wrappers:

```text
map_topologyTupleEdgeRawOrder_withDensity_formalRawOrderAbsDet_eq_restrict_rawSourceChart
map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_rawSourceChart
map_comp_topologyTupleEdgeRawOrder_withDensity_formalRawOrderAbsDet_eq_map_restrict_rawSourceChart
map_comp_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_map_restrict_rawSourceChart
```

Local-source wrappers:

```text
measure_map_restrict_retainedPassiveP13LocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_of_realization_of_cov
measure_map_restrict_retainedPassiveP13LocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_formalRawOrderAbsDet_of_realization
measure_map_restrict_retainedPassiveP13LocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_of_realization
```

## Content

The coordinate-level wrappers package the zero-tail and positive-tail retained
passive raw-order COV theorems over an arbitrary `M`, and push the weighted COV
through an arbitrary a.e.-measurable downstream map `psi`.

The local-source wrappers apply this to a realized fixed-base p.13
retained-passive source chart.  They replace the abstract source-side density
`topologyTupleEdgeRawOrderFDerivAbsDet` by either the formal raw-order
determinant density or the solved-`A1` product determinant density.

## Proof idea

For a realized source chart,

```text
mu = map sourceChart (m.restrict T)
```

restricts to the retained-passive local source because the realization
hypothesis puts `sourceChart y` in the local source for `m.restrict T`-a.e.
`y`.  The old abstract-density theorem proves this local restriction equals
the abstract weighted raw-order pushforward.  Both the old abstract COV and
the new formal/product COV identify their weighted pushforwards with
`map sourceChart (m.restrict T)`, so the local restriction also equals the
formal/product weighted pushforward.

## Nonclaims

No original source prior is constructed.  No signed-box source-density
identification is proved.  No normal-crossing theorem, pole-order theorem, or
RLCT theorem is claimed.  The canonical retained-passive local-source wrappers
are recorded in the follow-up canonical statement card.
