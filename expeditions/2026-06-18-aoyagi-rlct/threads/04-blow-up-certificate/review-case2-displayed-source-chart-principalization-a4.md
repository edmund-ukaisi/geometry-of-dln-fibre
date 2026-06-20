# Review - A4 Case 2 Displayed Source-Chart Principalization

Status: post-Lean xhigh review passed.

## Reviewers

Pre-Lean/read-only scouts:

- xhigh source/math scout `Sartre the 4th`.
- xhigh Lean/API scout `Kuhn the 4th`.

Post-Lean reviewers:

- xhigh Lean/API reviewer `Carver the 4th`.
- xhigh source/docs reviewer `Kierkegaard the 4th`.

## Source and Math Review

The source/math scout approved this checkpoint as source-faithful and useful
only as finite center bookkeeping. The source pattern is the displayed top-left
Case 2 chart:

```text
d_(J+1,J+1) = u,
d_ij = u * d'_ij  for off-pivot residual-block entries.
```

The finite center is restricted to rows `J+1..M(S)` and columns
`J+1..M^(S+1)`. The scout emphasized that principalization here means only the
finite residual-block center ideal, not the loss/Kullback ideal or an analytic
germ.

## Lean and API Review

The Lean/API scout confirmed that the math already existed in generic
selected-entry names and recommended adding this as a source-chart-map API
adapter. The global lemmas were placed after
`case2DisplayedSourceChartMap_eq_mul_normalized`, and the boundary projections
were placed in the later reopened
`Case2DisplayedSuppliedChartFamilyBoundary` namespace, after the source-chart
map definitions exist.

Post-Lean Lean/API review found no blocking or nonblocking issues. The
reviewer confirmed that the statements are honest wrappers over the existing
`selectedEntryChartMap` API, the namespace placement is acceptable, and the
checkpoint does not overclaim chart production, coverage, regularity,
Jacobians, or transitions.

Post-Lean source/docs review found no blocking source/math issues. Low findings
were documentation status drift in this review artifact and abbreviated caveats
in two compact ledgers; both are resolved in this checkpoint. The reviewer
confirmed top-left pivot scope, prefix-minimum rows, actual-width columns, and
finite residual-block center ideal scope.

## Required Caveats

- This uses the displayed top-left pivot `(J+1,J+1)`, not arbitrary source
  pivots.
- This principalizes only the finite residual-block center ideal.
- Pivot membership uses `1 <= S` and displayed continuation.
- This is not chart production, atlas coverage, coordinate regularity,
  Jacobian/volume arithmetic, normal crossings/RLCT, termination, transition
  invariance, or printed-vector repair.

## Verification

Pre-review focused Lean check:

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Post-Lean reviewer checks:

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `git diff --check`
- forbidden-token scan over `lean/DLNFibre/DLN/Aoyagi`
