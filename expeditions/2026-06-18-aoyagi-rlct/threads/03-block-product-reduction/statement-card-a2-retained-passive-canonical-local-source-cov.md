# Statement Card - A2 Retained-Passive Canonical Local-Source COV

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

## Lean Names

```text
measure_map_restrict_retainedPassiveP13CanonicalLocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_absDet
```

## Reproduction

```text
reproduction-a2-retained-passive-canonical-local-source-cov.md
```

## Claim

The canonical fixed-base retained-passive source edge-family map

```text
y |-> paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
        (ofTopologyTuple (topologyTupleEdgeRawOrderInverse y))
```

discharges the realization and a.e.-measurability hypotheses of the earlier
raw-order local-source COV theorem.  The resulting chart-produced measure
identity is

```text
mu.restrict localSource =
  Measure.map (sourceChart o topologyTupleEdgeRawOrder)
    ((m.restrict S).withDensity
      (fun z => ENNReal.ofReal
        (topologyTupleEdgeRawOrderFDerivAbsDet z))).
```

Here `mu = Measure.map sourceChart (m.restrict T)`, `T` is the raw-order
source-recursive determinant chart, and `localSource` is the retained-passive
local source for the identity edge-family readout.

## Method

For `y in T`, raw-order inversion gives `g y in S`.  The fixed-base
retained-passive realization theorem reads the canonical source edge family
back as `(ofTopologyTuple (g y)).edgeMatrix`.  The raw-order right-inverse
identity `topologyTupleEdgeRawOrder (g y) = y` then rewrites this edge family
as `edgeFamilyOfRawOrderTuple y`.

The same inverse-chart continuity, followed by `ofTopologyTuple` and the
continuous determinant-chart source chart, gives continuity of `sourceChart`
on `T`; the Borel target hypothesis gives the needed a.e.-measurability on
`m.restrict T`.

## Verification

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

Full `DLNFibre` build passed with pre-existing unrelated linter warnings.
`scripts/sorries` reported `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  `git diff --check` passed.  Independent xhigh read-only review
passed.

## Nonclaims

No original source-prior transport, selected-entry target-image equality,
source-rank coverage, explicit determinant formula, normal-crossing theorem,
pole-order theorem, or RLCT theorem is proved here.
