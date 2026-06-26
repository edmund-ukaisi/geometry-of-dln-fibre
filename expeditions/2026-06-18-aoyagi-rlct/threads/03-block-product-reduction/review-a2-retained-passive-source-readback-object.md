# Review - A2 Retained-Passive Source-Readback Object

Date: 2026-06-26.

Reviewer: xhigh read-only reviewer `Averroes the 3rd`.

Verdict: survived.

## Target

Lean and docs for the retained-passive source-readback object rung:

```text
RetainedPassiveNonredundantCoordinateData.ext_fields
RetainedPassiveNonredundantCoordinateData.sourceReadbackSuffixState
RetainedPassiveNonredundantCoordinateData.sourceReadbackTransformedEdge
RetainedPassiveNonredundantCoordinateData.sourceReadback
RetainedPassiveNonredundantCoordinateData.sourceReadback_edgeMatrix_eq
```

Files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
reproduction-a2-retained-passive-source-readback-object.md
statement-card-a2-retained-passive-source-readback-object.md
```

## Checks

The reviewer found no blocking mathematical or formalisation issue.  The
index shifts match the nonredundant retained-passive fields:

```text
A1passive p  reads transformed edge p.succ
F2 p         reads transformed edge p
A3passive p  reads transformed edge p.castSucc
C p          reads transformed edge p
Ctop, F3     read the suffix state at 0
```

The theorem `sourceReadback_edgeMatrix_eq` applies only to `data.edgeMatrix`
under `data.detChart` and proves fieldwise recovery using the established
determinant-chart readback theorem and `ext_fields`.

The documentation keeps the boundary explicit: the rung defines a total finite
readback map and proves inverse-on-image only.  It does not assert image
membership for arbitrary edge families, image openness, local homeomorphism,
source-rank coverage, source/image equality, measure pushforward,
density/Jacobian accounting, normal crossings, pole order, or RLCT.

## Verification

The reviewer ran the focused Lean check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
```

It completed successfully.  The reviewer also ran `git diff --check`
successfully.
