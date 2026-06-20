# A4 Case 2 Displayed Successor Gap Projections

Status: reproduced the displayed-boundary projections of successor invariant
bookkeeping already proved for source-selected Case 2 boundaries.

## Setup

The source-selected supplied Case 2 boundary already contains:

- supplied recurrence post-data for advancing from `(S,J)` to `(S,J+1)`;
- supplied corrected exponent post-data for the same advance;
- pre-state exponent certificates;
- the bridge `leastValue = level` on introduced labels;
- the old integer Case 2 least-value gap.

From these data, the source-selected boundary proves three successor facts:

```text
leastValue' = post.level  on labels introduced at (S,J+1),
leastValue' has the Case 2 gap at (S,J+1),
post.level has the Case 2 recurrence gap.
```

The displayed supplied boundary is exactly the source-selected boundary
specialized to the displayed pivot `(J+1,J+1)`.

## Reproduction

Let `data` be a displayed supplied Case 2 boundary. Its projection
`data.sourceSelectedBoundary` is a source-selected boundary with pivot
`(J+1,J+1)`.

Therefore:

```text
data.postLevelInvariants
  := data.sourceSelectedBoundary.postLevelInvariants,

data.successorLeastValueGap
  := data.sourceSelectedBoundary.successorLeastValueGap,

data.postCase2Gap
  := data.sourceSelectedBoundary.postCase2Gap.
```

No new algebra is hidden in this step. The underlying facts still depend on
the supplied recurrence post-data, the supplied corrected exponent post-data,
the old least-value/level bridge, and the old Case 2 gap.

## Scope / Caveats

- This is displayed-boundary projection bookkeeping only.
- The recurrence and exponent post-data are supplied fields.
- This does not prove that Aoyagi's affine chart produces those post-data.
- This does not prove chart coverage, coordinate regularity, Jacobian or
  volume-form exponents, normal crossings, RLCT extraction, termination, a
  transition invariant, or repair of the printed Case 2 vector mismatch.
