# Review - A2 Case 2 source chart-point coverage

Date: 2026-06-29.

## Verdict

PASS after one nonblocking docstring wording repair.

## Scope Reviewed

Lean:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean
```

Artifacts:

```text
reproduction-a2-case2-source-chart-point-coverage.md
statement-card-a2-case2-source-chart-point-coverage.md
```

## Source/Scope Review

Reviewer: Euclid the 4th, xhigh.

Verdict: PASS.  No required wording changes before banking.

The reproduction and statement card stay at finite residual-block chart-point
coverage.  They cite Aoyagi PDF pp. 19-22 only for the displayed selected-entry
substitution

```text
x_p = u,
x_i = u r_i     for i != p.
```

Both artifacts explicitly say the all-pivot statement is expedition-built
finite coordinate bookkeeping, not an Aoyagi-printed all-pivot analytic atlas.
The Lean docstrings for the two new theorems exclude analytic atlas coverage,
source production, normal crossings, pole order, and RLCT extraction.

Euclid noted one nearby nonblocking wording issue in the pre-existing wrapper
`exists_sourceSelectedChartMap_eq_value`: "source-coordinate production only"
could be read too close to source production.  The controller repaired that
docstring to "source-coordinate representation only" while retaining the
explicit nonclaim about source production of successor matrices or suffixes.

## Lean/API Review

Reviewer: Feynman the 4th, xhigh.

Verdict: PASS.  No required changes before banking.

The new theorems are useful Case 2 specializations of the generic all-pivot
selected-entry chart-point coverage theorem:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
  .exists_sourceChartPoint_chartMap_eq_value
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
  .exists_sourceChartPoint_chartMap_eq_value_and_coord_zero_eq_sourceSelected
```

The first theorem gives finite residual-block source chart-point coverage.  The
second theorem bundles that coverage with the existing coordinate readout
`coord_sourceChartPoint_eq_sourceSelected`.

The namespace collision risk is handled: the proof of the Case 2 wrapper uses
the local theorem intentionally, and the older `exists_sourceSelectedChartMap_eq_value`
wrapper now fully qualifies the generic theorem
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exists_sourceChartPoint_chartMap_eq_value`.

Feynman independently checked:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lake env lean -E warning DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean
```

Both passed.  The warning-as-error source check produced no diagnostics.

## Controller Verification

The controller checked:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre
scripts/sorries
git diff --check
rg -n 'sorry|axiom|native_decide|#exit|admit' <touched Aoyagi Lean files>
```

The full `DLNFibre` build passed via local `lake build` fallback.  The approved
`scripts/lb` path was attempted first but sandbox escalation for the shared
Lake semaphore/cache writes under `$HOME/.lake-shared` was rejected by the
environment policy; the existing `.lake/packages` symlink already pointed at
the shared store, so the fallback wrote only this worktree's local build
artifacts.

After the docstring wording repair, the controller reran the focused build:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
```

It passed.

Direct axiom probes for the two new declarations reported only:

```text
[propext, Classical.choice, Quot.sound]
```

## Nonclaims

This is finite residual-block chart-point coverage and coordinate postdata
only.  It proves no analytic atlas coverage, transition regularity, source
production of successor matrices or suffixes, source-prior transport,
determinant-chart Haar theorem, source-rank coverage, normal-crossing
extraction, pole order, or RLCT.
