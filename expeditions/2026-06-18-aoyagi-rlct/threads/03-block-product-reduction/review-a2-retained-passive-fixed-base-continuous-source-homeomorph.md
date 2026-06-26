# Review - A2 retained-passive fixed-base continuous source homeomorph

Date: 2026-06-26.

Reviewer: xhigh read-only reviewer `Jason the 4th`.

## Scope

Audit the fixed-base inverse/continuity bridges in
`lean/DLNFibre/DLN/Aoyagi/FixedBasepointChart.lean`, the retained-passive
continuous source edge-family set/readback/homeomorphism in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean`, and the associated
reproduction and statement-card notes.

Reviewed Lean artifacts:

```text
paperEndpointFixedBaseReverseEdgeFamilyOfMatrices_edgeMatrixOfReverseEdges
paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices_edgeMatrixOfReverseEdges
paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuous
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
paperEndpointFixedBaseRetainedPassiveP13SourceChart_mem_sourceEdgeFamilySet
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyReadback
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamily_homeomorph
```

## Verdict

PASS.  No blocking findings.

## Checks

The source boundary is preserved.  The new target is explicitly the fixed-base
continuous edge-family subtype cut out by `sourceRecursiveDetChartSet`, not a
source-rank stratum or original DLN source image.

The homeomorphism does not overclaim measure, Jacobian, normal-crossing,
pole-order, or RLCT content.  The module and docs state the nonclaims.

The fixed-base inverse and continuity lemma names match their content:
realisation after fixed-base matrix extraction recovers the original linear or
continuous edge family, and fixed-base edge-matrix extraction is continuous.

The continuous-edge homeomorphism is the expected fixed-base lift of the
existing matrix-level determinant/source-recursive chart homeomorphism.

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
