# Statement Card - A2 retained-passive fixed-base continuous source homeomorph

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/FixedBasepointChart.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean
```

## Lean Names

Fixed-base matrix/continuous-edge inverse bridges:

```text
paperEndpointFixedBaseReverseEdgeFamilyOfMatrices_edgeMatrixOfReverseEdges
paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices_edgeMatrixOfReverseEdges
paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuous
```

Retained-passive continuous source package:

```text
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
paperEndpointFixedBaseRetainedPassiveP13SourceChart_mem_sourceEdgeFamilySet
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyReadback
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamily_homeomorph
```

## Reproduction

```text
reproduction-a2-retained-passive-fixed-base-continuous-source-homeomorph.md
```

## Claim

The determinant-chart retained-passive coordinate subtype is homeomorphic to
the continuous fixed-base source edge-family set cut out by the
source-recursive determinant-chart condition on extracted edge matrices.

The forward map realises `data.edgeMatrix` as continuous reversed edge maps.
The inverse extracts fixed-base edge matrices and applies retained-passive
`sourceReadback`.  The left inverse is source readback of the named source
chart.  The right inverse uses matrix-level source readback reconstruction
and the fixed-base continuous realisation-after-extraction lemma.

## Method

The fixed-base inverse bridge is the basis cancellation
`Matrix.toLin_toMatrix`, first for linear edge maps and then for continuous
linear maps.  Continuity of fixed-base edge-matrix extraction follows from
the existing continuous-at coordinate theorem.

The retained-passive homeomorphism composes:

- the named coordinate-to-source edge-family map;
- fixed-base edge-matrix extraction;
- matrix-level `sourceReadback` on the source-recursive determinant-chart
  subtype;
- existing determinant-chart and source-recursive reconstruction theorems.

## Nonclaims

This is a homeomorphism onto the explicitly defined fixed-base continuous
source edge-family set.  It does not prove that arbitrary source-rank points
lie in that set, does not give source-rank coverage, source-image equality for
the original DLN source, finite determinant-chart cover, source-measure
pushforward, density/Jacobian accounting, selected-entry residual-factor
compatibility, normal crossings, pole order, or RLCT extraction.

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
review-a2-retained-passive-fixed-base-continuous-source-homeomorph.md
```
