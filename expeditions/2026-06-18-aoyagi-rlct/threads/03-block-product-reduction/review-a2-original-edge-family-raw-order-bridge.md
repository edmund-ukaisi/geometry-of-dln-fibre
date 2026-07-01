# Review - A2 Original Edge-Family Raw-Order Bridge

Date: 2026-07-01.

Reviewer: xhigh sidecar `Hypatia the 2nd`.

## Verdict

PASS. No required changes.

## Checks

The Lean statements match their content.  The bridge is a full ambient
linear/continuous-linear coordinate equivalence from raw-order tuple
coordinates to original matrix tuple coordinates.  It is not the nonlinear
retained-passive chart map `topologyTupleEdgeRawOrder`.

The p.13 source-chart theorems keep the correct domain hypothesis:

```text
y ∈ topologyTupleRawOrderSourceRecursiveDetChartSet
```

This is necessary because the public raw-order p.13 source chart is defined
through `topologyTupleEdgeRawOrderInverse`.

The row/column reindexing orientation is correct.  Rows use `p.succ` and
columns use `p.castSucc`, matching the existing p.13 fixed-basis edge-matrix
readout and the original tuple convention:

```text
Matrix.reindex (e p.succ) (e p.castSucc)
```

The module defines no measure theorem and introduces no hidden
restricted-Haar claim.  Its docstring explicitly excludes restricted
determinant/source-chart Haar transport and chart-produced source-image
measure comparison.

## Next Measure Boundary

The next honest measure theorem remains a restricted pushforward/scalar
comparison.  For the new continuous linear equivalence `L` and an ambient
raw-coordinate Haar measure `m`, compare

```text
Measure.map L (m.restrict rawSourceSet)
```

with a positive scalar multiple of `originalTupleVolume` restricted to
`L '' rawSourceSet`.  Do not assert that the restricted source/determinant
chart measure itself is Haar.

## Reviewer Verification

Review was read-only.  Controller verification separately ran focused Lean,
focused module build, aggregator elaboration, full `DLNFibre` build,
`scripts/sorries`, `git diff --check`, and direct axiom probes.
