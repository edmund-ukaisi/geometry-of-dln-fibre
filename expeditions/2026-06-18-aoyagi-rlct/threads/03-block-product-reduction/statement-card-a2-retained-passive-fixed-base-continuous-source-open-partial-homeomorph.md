# Statement Card - A2 retained-passive fixed-base continuous source open partial homeomorph

## Lean File

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean
```

## Lean Names

```text
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
paperEndpointFixedBaseRetainedPassiveP13LocalSource_eq_preimage_sourceEdgeFamilySet
paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceEdgeFamilyOfData_eq
isOpen_paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamily_openPartialHomeomorph
```

## Reproduction

```text
reproduction-a2-retained-passive-fixed-base-continuous-source-open-partial-homeomorph.md
```

## Claim

The fixed-base retained-passive p.13 continuous source edge-family chart is an
ambient `OpenPartialHomeomorph`.  Its source is exactly the retained-passive
determinant chart `detChartSet`; its target is exactly the fixed-base
continuous edge-family set whose extracted edge matrices satisfy
`sourceRecursiveDetChartSet`.

The parameterized local source used elsewhere is the preimage of this target
under a chosen source edge-family map `Cedge`.

## Method

The forward ambient map realises `data.edgeMatrix` as continuous reversed
fixed-base edges.  The inverse extracts fixed-base edge matrices and applies
`sourceReadback`.

The source-to-target and left-inverse fields use the existing determinant
chart readback theorem.  The target-to-source and right-inverse fields use
matrix-level source-recursive reconstruction plus the fixed-base
realisation-after-extraction theorem.  The target is open as the preimage of
the open matrix-level `sourceRecursiveDetChartSet` under continuous fixed-base
edge-matrix extraction.

## Nonclaims

This is an open chart object for the explicitly defined fixed-base
retained-passive source model.  It does not prove source-rank coverage,
source-image equality for the original DLN source, finite cover assembly,
source-measure pushforward, density/Jacobian accounting, selected-entry
residual-factor compatibility, normal crossings, pole order, or RLCT
extraction.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalSource
```

Full check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
```

Both passed on 2026-06-26, with the existing repository warning stream.
`scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`, and
`git diff --check` passed.

Review:

```text
review-a2-retained-passive-fixed-base-continuous-source-open-partial-homeomorph.md
```
