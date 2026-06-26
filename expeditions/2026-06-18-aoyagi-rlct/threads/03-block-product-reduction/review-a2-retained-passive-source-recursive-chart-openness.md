# Review - A2 retained-passive source-recursive chart openness

Date: 2026-06-26.

Reviewers: xhigh `Heisenberg the 3rd`.

## Scope

Audit the source-recursive determinant chart openness additions in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
reproduction-a2-retained-passive-source-recursive-chart-openness.md
statement-card-a2-retained-passive-source-recursive-chart-openness.md
```

## Verdict

Passed.

## Findings

The proof has the expected shape.  The algebra file names the chart set and
the proof-irrelevance equivalence

```text
sourceRecursiveDetChart_iff.
```

The topology file proves a pointwise neighborhood theorem

```text
sourceRecursiveDetChartSet_mem_nhds
```

using `continuousAt_sourceReadbackTransformedEdge`, the generic
`identityCornerDetChart_mem_nhds`, and finite `Filter.iInter_mem`.  The open
set theorem is then immediate by `isOpen_iff_mem_nhds`.

The reviewer found no issues.  In particular, the proof-irrelevance step in
`sourceRecursiveDetChart_iff` correctly replaces an arbitrary
`hp : p.succ <= Fin.last _` by the canonical `p.succ.le_last`, and the
canonical `sourceReadbackTransformedEdge` unfolds to the same suffix state.

## Nonclaims Check

The statement is only ambient openness of the named recursive determinant
chart.  It does not assert equality with the whole source image, source-rank
coverage, measure pushforward, density/Jacobian transport, normal crossings,
pole order, or RLCT extraction.

## Verification

Focused checks passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
```

Full and hygiene checks passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
scripts/sorries
git diff --check
```
