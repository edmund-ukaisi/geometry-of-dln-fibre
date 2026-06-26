# Review - A2 retained-passive open partial homeomorphism

Date: 2026-06-26.

Reviewers: xhigh `Helmholtz the 3rd`.

## Scope

Audit the retained-passive open-partial-homeomorphism additions in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
reproduction-a2-retained-passive-open-partial-homeomorph.md
statement-card-a2-retained-passive-open-partial-homeomorph.md
```

## Verdict

Passed.

## Findings

No findings.

The set-subtype homeomorphism only relabels the earlier predicate-subtype
homeomorphism via `mem_detChartSet` and `mem_sourceRecursiveDetChartSet`.

The `OpenPartialHomeomorph` has exactly source `detChartSet`, target
`sourceRecursiveDetChartSet`, forward map `edgeMatrix`, and inverse map
`sourceReadback`.  Its source/target mapping fields and inverse-law fields are
backed by the existing finite chart/readback theorems.

The continuity fields are sound.  Forward continuity is transported through
`Homeomorph.ofEqSubtypes` from `continuous_edgeMatrix_detChart_subtype`;
inverse continuity uses `continuousAt_sourceReadback` with the identity
edge-family map and then weakens to `ContinuousWithinAt`.

## Review Questions

1. Does `detChartSet_sourceRecursiveDetChartSet_homeomorph` only rewrite the
   existing subtype homeomorphism along the named-set membership equivalences?
2. Does `detChart_sourceRecursiveDetChart_openPartialHomeomorph` have exactly
   source `detChartSet`, target `sourceRecursiveDetChartSet`, forward
   `edgeMatrix`, and inverse `sourceReadback`?
3. Are all map-source, map-target, left-inverse, and right-inverse fields
   justified by already proved finite chart theorems?
4. Are the continuity fields real topology statements rather than vacuous
   wrappers?
5. Are the nonclaims strong enough to avoid source-image, source-rank,
   measure/Jacobian, normal-crossing, pole-order, or RLCT overclaim?

## Verification

Focused check passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
```

The reviewer did not rerun Lean.  Controller full and hygiene checks passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
scripts/sorries
git diff --check
```
