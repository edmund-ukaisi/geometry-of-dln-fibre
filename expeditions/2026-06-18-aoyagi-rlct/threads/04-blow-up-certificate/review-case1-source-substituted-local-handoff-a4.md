# Review - A4 Case 1 source-substituted local handoff

Status: reviewed by controller and xhigh reviewer; pass with minor documentation
wording tightened.

## Math Review

The theorem is a rewrite of an already proved local handoff, using the
selected-old source substitution boundary plus first-jump level identification.
It does not add a new recurrence calculation: after transporting
`data.firstJump` along `hlevel : level = factoredBase.level`, the calculation is

```text
source.step = mulStepAt factoredBase.step u (J+J1).
```

The left diagonal is therefore correctly rewritten from explicit
`mulStepAt` weights to `source.weight` on residual row levels.

## Lean/API Review

The theorem keeps all nontrivial identifications explicit. In particular,
`Case1DisplayedRowStripSuppliedTransitionBoundary` has an abstract `level`
map, and the selected-old source substitution boundary uses
`factoredBase.level`; the new theorem requires `level = factoredBase.level`.

The result remains a supplied local handoff. The matrix block, pivot equation,
source state, factored-base state, post state, recurrence post-data, and
exponent post-data are all supplied.

## Xhigh Review

The independent xhigh review found no blocking formalisation or source-fidelity
issue. It confirmed that the rewrite is justified by
`hsource.step_eq_mulStepAt_of_firstJump` after transporting the first-jump
hypotheses via `hlevel`, and that the off-by-one convention is consistent:
`monomialRec` uses steps strictly below the row index, so the factor at level
`J+J1` first affects row `J+J1+1`, matching the Case 1 strip boundary. The
review recommended tightening the reproduction wording to keep residual-row
indices separate from source row levels; that wording has been updated.

## Caveats

- This does not construct the source pullback.
- This does not construct the selected-old chart.
- This does not identify the hidden old label behind the `Unit` center
  generator.
- This does not prove chart-produced post-data, chart coverage, regularity,
  Jacobian accounting, normal crossings, or RLCT extraction.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
  passed.
- From `lean/`: `lake build DLNFibre` passed.
- From `lean/`: `./scripts/sorries`: `0 sorry`, `0 #exit`,
  `0 native_decide`, `0 axiom`.
- From repository root: `git diff --check` passed.
