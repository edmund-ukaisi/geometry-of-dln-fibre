# Review - A2 retained-passive source-recursive chart homeomorphism

Date: 2026-06-26.

Reviewers: xhigh `Pascal the 3rd`.

## Scope

Audit the source-recursive chart packaging additions in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
reproduction-a2-retained-passive-source-recursive-chart-homeomorph.md
statement-card-a2-retained-passive-source-recursive-chart-homeomorph.md
```

## Verdict

Passed.

## Findings

The target is correctly scoped: it is a homeomorphism between two explicit
subtypes, not a claim about the whole source image.

The key algebraic new theorem is

```text
sourceRecursiveDetChart_edgeMatrix_of_detChart.
```

The reviewer confirmed the proof route: replace the arbitrary proof
`hp : p.succ <= Fin.last (M + 1)` by `p.succ.le_last` by proof irrelevance,
then use the existing bundled transformed-edge readback theorem for
`data.toCoordinateData`.  The theorem identifies the transformed-edge
top-left corner with `(data.toCoordinateData).solvedA1 p`.  The moved
algebraic lemma

```text
solvedA1_det_isUnit_of_detChart.
```

then supplies the determinant-unit side condition, including the active
`p = 0` block by tail-inverse times `Ctop` and the passive blocks by the
stored passive determinant units.

The reviewer also confirmed that moving `solvedA1_det_isUnit_of_detChart` from
the topology file into `RetainedPassiveCoordinates.lean` is the right
dependency direction.  The topological wrappers use `.subtype_mk` on the
already banked ambient continuity theorems, and the homeomorphism inverse laws
use the already banked two-sided finite inverse theorems by `Subtype.ext`.

## Nonclaims Check

The statement does not assert that `sourceRecursiveDetChart` is open in the
ambient edge-family space.  It does not assert equality with the whole source
image, source-rank coverage, measure pushforward, density/Jacobian transport,
normal crossings, pole order, or RLCT extraction.

## Verification

Focused and full controller checks passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
scripts/sorries
git diff --check
```

The full build emitted only pre-existing linter warnings from unrelated
Core/downstream files.
