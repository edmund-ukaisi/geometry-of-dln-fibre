# Review - A2 retained-passive fixed-base continuous source open partial homeomorph

Date: 2026-06-26.

Reviewer: xhigh read-only reviewer `Maxwell the 4th`.

## Scope

Audit the ambient retained-passive fixed-base continuous source
`OpenPartialHomeomorph` in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean` and the associated
reproduction and statement-card notes.

Reviewed Lean artifacts:

```text
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
paperEndpointFixedBaseRetainedPassiveP13LocalSource_eq_preimage_sourceEdgeFamilySet
paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceEdgeFamilyOfData_eq
isOpen_paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamily_openPartialHomeomorph
```

## Verdict

PASS.  No blocking findings.

## Checks

The source and target are exact: the target is the fixed-base edge-family
preimage of `sourceRecursiveDetChartSet`, and the partial homeomorphism source
and target are exactly `detChartSet` and that target set.

The inverse laws are chart-scoped.  `map_source'` uses `data.detChart`;
`map_target'` uses target membership to obtain `sourceRecursiveDetChart`; and
the right inverse is stated only on the target.

No source-boundary overclaim was found.  The Lean docstring and docs explicitly
exclude source-rank coverage, source-image equality, measure/Jacobian
transport, normal crossings, pole order, and RLCT extraction.

The statement matches the recorded Aoyagi boundary: pp. 10-13 support the
block substitutions and product algebra, not measure pushforward,
density/Jacobian transport, source image/coverage, or RLCT extraction.

## Verification

Controller checks:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalSource
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
scripts/sorries
git diff --check
```

Both Lean builds passed on 2026-06-26, with the existing repository warning
stream.  `scripts/sorries` reported
`0 sorry, 0 #exit, 0 native_decide, 0 axiom`, and `git diff --check` passed.
