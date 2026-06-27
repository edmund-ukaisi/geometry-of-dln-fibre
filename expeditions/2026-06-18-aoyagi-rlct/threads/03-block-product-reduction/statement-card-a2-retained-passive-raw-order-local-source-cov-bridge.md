# Statement Card - A2 Retained-Passive Raw-Order Local-Source COV Bridge

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

## Lean Names

```text
paperEndpointFixedBaseRetainedPassiveP13LocalSource_mem_of_edgeFamilyOfRawOrderTuple_realization
measure_map_restrict_retainedPassiveP13LocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_absDet_of_realization
```

## Reproduction

```text
reproduction-a2-retained-passive-raw-order-local-source-cov-bridge.md
```

## Claim

Under an explicit fixed-base realization map from raw-order target coordinates
to the retained-passive p.13 parameter space, the retained-passive weighted
raw-order COV theorem can be read as a local-source chart-produced measure
identity.

The target local measure is

```text
mu = Measure.map sourceChart (m.restrict T),
```

where `T` is the raw-order source-recursive determinant chart.  If
`sourceChart` is a.e.-measurable on `m.restrict T` and its fixed-base edge
matrices realize `edgeFamilyOfRawOrderTuple y` for every `y in T`, then

```text
mu.restrict localSource =
  Measure.map (fun z => sourceChart (topologyTupleEdgeRawOrder z))
    ((m.restrict S).withDensity (ofReal o J)).
```

Here `S` is the tuple determinant chart and `J` is the forward absolute
Jacobian determinant.

## Role

This bridges the landed chart-coordinate weighted COV theorem into the
`mu.restrict localSource = Measure.map sourceChart ...` orientation used by
the retained-passive local-measure consumers, without pretending to construct
the original source prior.

## Nonclaims

No determinant-density continuity, inverse-density measurability, original DLN
source-prior transport, selected-entry target-image theorem, source-rank
coverage, normal crossing, pole order, or RLCT statement is part of this slice.

## Verification

Review accepted in
`review-a2-retained-passive-raw-order-local-source-cov-bridge.md`.

Focused Lean build passed:

```text
cd lean && env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure
```

Full verification passed:

```text
cd lean && env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
