# Statement card - A4 Case 1 displayed row-strip quotients

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`ddc31887100fcf9cdc3ec933661938b42509363c`.

Names:

- `DLNFibre.DLN.Aoyagi.exists_case1DisplayedRowStripPivot_quotients_of_rowIndex_monomialRec`
- `DLNFibre.DLN.Aoyagi.exists_case1DisplayedRowStripPivot_pivotMul_quotients_of_rowIndex_monomialRec`
- `DLNFibre.DLN.Aoyagi.exists_case1DisplayedRowStripPivot_pivotMul_quotients_of_recurrenceState`
- `DLNFibre.DLN.Aoyagi.exists_case1RowStrip_sourceOrder_identity_of_rowIndex_monomialRec`
- `DLNFibre.DLN.Aoyagi.exists_case1DisplayedRowStrip_sourceOrder_identity_of_rowIndex_monomialRec`

## Statement

Lean now chooses quotient witnesses for the displayed Case 1(2) row-strip
`P` matrix from monomial recurrence divisibility.

For the displayed top-left pivot row, every residual row level is at least
`J+1`.  Therefore the recurrence weight at the pivot row divides every later
residual-row recurrence weight.  The common selected variable is kept on both
sides:

```text
u * monomialRec step rowLevel_i
  = q_i * (u * monomialRec step (J+1)).
```

No cancellation of `u`, inverse, or division is used.

The source-order wrappers feed these witnesses into the previously proved
Case 1(2) row-strip weighted source identity.  The normalised matrix, strip
predicate, hidden old-variable factorisation convention, and following factor
remain supplied.

## Source Role

Aoyagi displays `P` entries using `b'_i / b'_(J+1)` and calls the matrix
regular.  This checkpoint supplies the elementary monomial-divisibility
certificate behind those quotients for the displayed top-left pivot.

## Proved

- Monomial recurrence weights admit right-oriented quotient witnesses from the
  displayed pivot level `J+1` to every residual row level.
- Corresponding right-oriented witnesses exist after common multiplication by
  the selected variable `u`.
- A packaged recurrence state supplies the same quotient shape for
  `state.case2ResidualRowWeight`.
- The quotient witnesses can be fed into the Case 1(2) row-strip source-order
  `Q/P` identity.

## Assumed

- The recurrence step data is supplied.
- The selected variable has already been normalised so it is counted once.
- The displayed pivot matrix is already normalised.
- The strip predicate and following factor are supplied.

## Not Proved

- No selected-entry chart construction or chart coverage.
- No hidden old-label validity or factorisation production.
- No recurrence/exponent post-data.
- No chart regularity, transition regularity, or Jacobian formula.
- No normal crossings or RLCT extraction.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case1-displayed-row-strip-quotients-a4.md`.
- Review artifact:
  `review-case1-displayed-row-strip-quotients-a4.md`.

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
