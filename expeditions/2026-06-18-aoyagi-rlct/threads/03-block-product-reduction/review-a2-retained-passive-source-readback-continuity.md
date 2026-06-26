# Review - A2 retained-passive source-readback continuity

Date: 2026-06-26.

Reviewer: xhigh `Beauvoir the 3rd`.

## Scope

Audit the finite source-readback continuity rung in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
reproduction-a2-retained-passive-source-readback-continuity.md
statement-card-a2-retained-passive-source-readback-continuity.md
```

## Verdict

Passed.  No formalisation or mathematical issues were found.

## Findings

The determinant predicate is exactly scoped.  `sourceRecursiveDetChart`
requires `identityCornerDetChart` only for each transformed edge visited by
the suffix-state recursion with terminal index `Fin.last (M+1)`.  It does not
assert image membership, source-rank coverage, or source/image equality.

The continuity layering is correct: the Lean development proves
`ContinuousAt` suffix-state/readback helpers first and derives subtype
continuity afterward.  The proofs use the existing suffix-state API directly:
`continuousAt_chartLocalSuffixState_suffixState_fields` and
`continuousAt_chartLocalSuffixState_residualBlock`.

The index shifts are correct.  The readback uses `p.succ` for `A1passive`,
`p` for `F2` and `C`, `p.castSucc` for `A3passive`, and suffix state `0` for
`Ctop` and `F3`.

No hidden claim of image openness, local homeomorphism, source-rank coverage,
measure pushforward, density/Jacobian transport, normal crossings, pole order,
or RLCT extraction was found.

## Verification

The reviewer reran the focused topology build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
```

It passed.
