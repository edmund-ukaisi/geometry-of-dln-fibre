# Statement card - A4 Case 1 source-weight factored boundary

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`1ff9fba745d981cb6305b9afdf05f78788ecee8a`.

Names:

- `DLNFibre.DLN.Aoyagi.case1ResidualRowStrip`
- `DLNFibre.DLN.Aoyagi.case1ResidualRowStrip_decidablePred`
- `DLNFibre.DLN.Aoyagi.case1RowStripOldWeight_eq_monomialRec_mulStepAt_of_level`
- `DLNFibre.DLN.Aoyagi.case1ResidualRowStripOldWeight_eq_sourceMulStepAt`
- `DLNFibre.DLN.Aoyagi.case1ResidualRowStrip_diagonal_mul_sourceMatrix_sourceWeights`

## Statement

Lean now identifies the displayed Case 1(2) row-strip old-weight convention
with the original source recurrence after substituting the old selected
variable as `old = u * old'`.

The canonical residual-row strip is

```text
case2ResidualRowLevel i <= J + J1.
```

For rows in that strip, the old source factor at level `J+J1` has not yet
entered the recurrence. Below the strip it has entered once, giving the common
factor `u`.

## Source Role

This is the source-side companion to the factored-base post-data boundary. It
explains why the displayed source matrix uses divided entries on strip rows
and old row weights with a hidden factor on lower residual rows.

## Proved

- The canonical residual-row strip predicate.
- The row-strip old-weight convention equals `monomialRec (mulStepAt step u
  (J+J1))` evaluated at residual row levels.
- The row-strip source-matrix identity can be stated with the original source
  recurrence on the left diagonal.

## Not Proved

- No construction of the factored-base recurrence from source coordinates.
- No hidden old-label source-validity proof.
- No chart construction, coverage, regularity, or Jacobian formula.
- No post-data production theorem.
- No normal crossings or RLCT extraction.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case1-source-weight-factored-boundary-a4.md`.
- Review artifact:
  `review-case1-source-weight-factored-boundary-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:
  passed.
- From `lean/`: `lake build DLNFibre`: passed, with only pre-existing Core
  warnings.
- From `lean/`: `./scripts/sorries`: `0 sorry`, `0 #exit`,
  `0 native_decide`, `0 axiom`.
- From the worktree root: `git diff --check`: passed.
- Forbidden-token scan over `lean/DLNFibre/DLN/Aoyagi` and the expedition
  directory found no Lean forbidden-token use; hits are existing prose
  mentions in expedition notes and statement cards.
