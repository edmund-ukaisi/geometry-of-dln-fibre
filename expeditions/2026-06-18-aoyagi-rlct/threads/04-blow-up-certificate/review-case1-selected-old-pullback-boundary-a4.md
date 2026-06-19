# Review - A4 Case 1 selected-old pullback boundary

Status: reviewed by controller and xhigh reviewer; pass after one
documentation correction.

## Math Review

The package is intentionally an assumption interface. It combines two already
separated supplied boundaries:

- selected-old pullback recurrence data, where `source` is the recurrence after
  `old = u * old'`;
- the displayed row-strip local handoff, now specialized to
  `factoredBase.level`.

The only new calculation exposed by the package is a projection of an existing
calculation:

```text
source.step = mulStepAt factoredBase.step u (J+J1).
```

The source-order identity is also a projection of the previous
source-substituted local handoff with the level equality specialized to `rfl`.

## Lean/API Review

The package removes an avoidable API seam: downstream callers no longer need a
separate `level = factoredBase.level` argument when they use this combined
Case 1(2) boundary. It does not add chart regularity or chart coverage fields.

The `Unit` center generator and the source label `(s0,k0)` are kept separate:
center membership is finite bookkeeping, while introduced-label validity and
selected level come from the supplied pullback/local fields.

## Xhigh Review

The independent xhigh review found no blocking Lean or math issue. It confirmed
that specializing the bundled handoff to `factoredBase.level` is an honest
interface narrowing, not a proof of a hidden equality; the source-order
projection simply passes `rfl` to the older equality-taking theorem. It also
confirmed that the projections repackage supplied consequences only, that no
theorem statement makes the `Unit` center token determine `(s0,k0)`, and that
the off-by-one convention is consistent with the selected old factor at level
`J+J1` affecting rows below the Case 1 strip.

The review did find one documentation error in `priorities.md`, where the
package was described as still assuming chart production. That was corrected:
chart production remains open and is not a field of this package.

## Caveats

- This does not construct the source pullback from raw coordinates.
- This does not construct the selected-old chart or an affine blow-up atlas.
- This does not prove chart-produced post-data.
- This does not prove chart coverage, regularity, transition regularity,
  Jacobian accounting, normal crossings, or RLCT extraction.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
  passed.
- From `lean/`: `lake build DLNFibre` passed.
- From `lean/`: `./scripts/sorries`: `0 sorry`, `0 #exit`,
  `0 native_decide`, `0 axiom`.
- From repository root: `git diff --check` passed.
