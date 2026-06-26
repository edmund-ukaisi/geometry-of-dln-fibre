# Review - A2 Retained-Passive Solved-A1 Continuity

Date: 2026-06-26.

Reviewer: xhigh read-only reviewer `Popper the 3rd`.

Verdict: survived.

## Target

Lean and docs for the retained-passive solved-`A1` continuity rung:

```text
RetainedPassiveNonredundantCoordinateData.continuous_retainedPassiveA1TailAfterFirst
RetainedPassiveNonredundantCoordinateData.continuous_solvedA1_detChart_subtype
```

Files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
reproduction-a2-retained-passive-solved-a1-continuity.md
statement-card-a2-retained-passive-solved-a1-continuity.md
```

## Checks

The reviewer found that `continuous_retainedPassiveA1TailAfterFirst` proves
only continuity of the finite passive top-left tail product.  The proof is the
constant identity base case plus the `residualFactorProduct_castSucc`
recurrence and continuous matrix multiplication.

The reviewer found that `continuous_solvedA1_detChart_subtype` uses exactly
the expected determinant-chart ingredients.  The zero component uses tail
continuity, passive `A1` determinant-unit data via
`toCoordinateData_passiveA1_units`,
`retainedPassiveA1TailAfterFirst_det_isUnit_of_passive`, matrix-inverse
continuity, and multiplication by `Ctop`.  Nonzero components reduce to
`A1seed`.

The typeclass assumptions are reasonable for this rung.  The tail-only theorem
could be weaker, but `[NontriviallyNormedField K] [Fintype ρ] [DecidableEq ρ]`
matches the matrix-inverse continuity API used by the subtype theorem and the
nearby topology file.

The docs and ledger updates stay within the nonclaim boundary.  They do not
claim continuity of `solvedA3`, `toCoordinateData`, or `edgeMatrix`; they also
avoid image openness, source coverage/equality, measure/Jacobian transport,
normal crossings, pole order, and RLCT.

## Verification

The reviewer ran the focused Lean check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
```

It completed successfully.  The reviewer also ran `git diff --check`
successfully.
