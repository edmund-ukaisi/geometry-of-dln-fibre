# Review - A2 Retained-Passive Projection Continuity

Date: 2026-06-26.

Reviewer: xhigh read-only reviewer `Parfit the 3rd`.

Verdict: survived.

## Target

Lean and docs for the retained-passive projection-continuity rung:

```text
RetainedPassiveNonredundantCoordinateData.continuous_A1passive
RetainedPassiveNonredundantCoordinateData.continuous_F2
RetainedPassiveNonredundantCoordinateData.continuous_A3passive
RetainedPassiveNonredundantCoordinateData.continuous_C
RetainedPassiveNonredundantCoordinateData.continuous_Ctop
RetainedPassiveNonredundantCoordinateData.continuous_F3
RetainedPassiveNonredundantCoordinateData.continuous_A1seed
RetainedPassiveNonredundantCoordinateData.continuous_F2full
RetainedPassiveNonredundantCoordinateData.continuous_A3seed
```

Files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
reproduction-a2-retained-passive-projection-continuity.md
statement-card-a2-retained-passive-projection-continuity.md
```

## Checks

The reviewer found that the Lean diff is limited to product projections and
dummy-slot component continuity.  The stored-field theorems are projections
and finite-family evaluations from `topologyTuple`.  The dummy-slot theorems
split on `Fin` cases and use either a stored-field projection theorem or
`continuous_const`.

The typeclass assumptions are scoped correctly: stored projections need only
`[TopologicalSpace K]`; the zero-filled component maps use
`[CommRing K] [TopologicalSpace K]`, matching the zero-filled definitions.

The docs and ledger updates stay within the nonclaim boundary.  They do not
claim continuity of `solvedA1`, `solvedA3`, `toCoordinateData`, or
`edgeMatrix`; they also avoid image openness, coverage, measure/Jacobian
transport, normal crossings, pole order, and RLCT.

## Verification

The reviewer ran the focused Lean check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
```

It completed successfully.
