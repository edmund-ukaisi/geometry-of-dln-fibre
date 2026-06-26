# Review - A2 Retained-Passive Solved-A3 Continuity

Date: 2026-06-26.

Reviewer: xhigh read-only reviewer `Sartre the 3rd`.

Verdict: survived.

## Target

Lean and docs for the retained-passive solved-`A3` continuity rung:

```text
RetainedPassiveNonredundantCoordinateData.continuous_retainedPassiveA3WithoutLast
RetainedPassiveNonredundantCoordinateData.continuous_residualFactorProduct_C
RetainedPassiveNonredundantCoordinateData.solvedA1_det_isUnit_of_detChart
RetainedPassiveNonredundantCoordinateData.continuous_residualFactorProduct_solvedA1_detChart_subtype
RetainedPassiveNonredundantCoordinateData.residualFactorProduct_solvedA1_det_isUnit_of_detChart
RetainedPassiveNonredundantCoordinateData.continuous_retainedPassiveLowerLeftProductTailSum_detChart_subtype
RetainedPassiveNonredundantCoordinateData.continuous_solvedA3_detChart_subtype
```

Files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
reproduction-a2-retained-passive-solved-a3-continuity.md
statement-card-a2-retained-passive-solved-a3-continuity.md
```

## Checks

The reviewer found that the Lean diff stays within the intended scope: finite
product/tail support lemmas and componentwise `solvedA3` continuity on
`{data // data.detChart}`.

Inverse continuity in this rung is used only for solved-`A1` residual
products, guarded by determinant-unit support from the solved-`A1` unit
propagation theorem.  The typeclass assumptions are reasonable for finite
matrix products, determinants, and inverse continuity over a
`NontriviallyNormedField`.

The docs and ledger updates keep the nonclaim boundary explicit.  They do not
claim `edgeMatrix` continuity, image openness, source-rank coverage,
source/image equality, measure/Jacobian results, normal crossings, pole order,
or RLCT.

## Verification

The reviewer ran the focused Lean check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
```

It completed successfully.  The reviewer also ran `git diff --check`
successfully.
