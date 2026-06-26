# Review - A2 Retained-Passive Edge-Matrix Continuity

Date: 2026-06-26.

Reviewer: xhigh read-only reviewer `Galileo the 3rd`.

Verdict: survived.

## Target

Lean and docs for the retained-passive source-map continuity rung:

```text
RetainedPassiveNonredundantCoordinateData.continuous_edgeMatrix_detChart_subtype_apply
RetainedPassiveNonredundantCoordinateData.continuous_edgeMatrix_detChart_subtype
```

Files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
reproduction-a2-retained-passive-edge-matrix-continuity.md
statement-card-a2-retained-passive-edge-matrix-continuity.md
```

## Checks

The reviewer found that the theorem statements match the intended scope:
per-edge continuity of `data.1.edgeMatrix p` on `{data // data.detChart}`,
and the Pi-family wrapper for `data.1.edgeMatrix`.

The proof uses the banked solved-`A1` and solved-`A3` continuity theorems,
the `F2full` and `C` projection-continuity theorems, and matrix continuity
for `fromBlocks`, multiplication, negation, and subtraction.  The reviewer
checked the two `F2` indices:

```text
p.castSucc  -- current transformed-edge block
p.succ      -- next suffix/base-change block in the left multiplier
```

The final unfolding step was accepted by Lean and matches the definitions of
`edgeMatrix`, `RetainedPassiveCoordinateData.edgeMatrix`,
`retainedPassiveFixedBaseEdgeMatrix`, and `toCoordinateData`.

The nonclaim boundary is clean.  The rung does not assert image openness,
source-rank coverage, source/image equality, local homeomorphism, measure
pushforward, density/Jacobian accounting, normal crossings, pole order, or
RLCT.

## Verification

The reviewer ran the focused Lean check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
```

It completed successfully.  The reviewer also ran `git diff --check`
successfully and scanned the new docs for trailing whitespace and placeholder
markers.
