# Review - A4 Case 1 displayed row-strip weighted source

Status: reviewed; no blockers found.

## Reviewers

- Source scout: `Herschel the 3rd`.
- Pen-and-paper scout: `Socrates the 3rd`.
- Lean/API scout: `Pauli the 3rd`.
- Implementation reviewer: `Noether the 3rd`.

## Source And Math Review

The source scout checked Aoyagi PDF pp. 16-19.  Case 1(2) displays only the
top-left row-strip chart `d_(J+1,J+1)`.  The row strip
`J+1..J+J1` is divided by the new selected variable `u_(S,J+1)`, while lower
residual rows `J+J1+1..M(S)` are not divided before the `Q` operation.  The
hidden old variable is factored as

```text
u_(s,k)=u_(S,J+1)u'_(s,k).
```

The pen-and-paper scout reproduced the weighted source identity.  With `A`
the already normalised pre-`Q` matrix,

```text
d_ij = u A_ij        on the row strip,
d_ij = A_ij          below the row strip.
```

The old row weights are `c_i` on the strip and `u c_i` below the strip, so

```text
oldWeight_i d_ij = (u c_i) A_ij
```

for every residual row.  The selected variable is counted once.

## Lean/API Review

The Lean/API scout recommended a supplied-data boundary rather than a chart
production theorem.  The implemented code follows that boundary:

- the elementary row-strip weighting identity is proved generically;
- pivot-first transport turns it into a `WeightedPivotFirstSubstitutionData`
  source equality;
- quotient witnesses remain supplied;
- the Case 1-specific wrapper only projects source-validity facts from
  `Case1FirstJumpHypotheses` and applies the already supplied source-order
  identity.

The implementation reviewer found no blocking issue and confirmed that the
statements do not double-count `u`.  One clarity issue was fixed before
commit: the `case1RowStripSourceMatrix` docstring now says `A` is already
normalised and that the definition reconstructs old source entries.

## Caveats

- `Case1DisplayedRowStripSuppliedWeightedSourceData.weighted` is arbitrary
  supplied `WeightedPivotFirstSubstitutionData`; the type does not enforce
  that it was produced by `case1RowStrip_weightedPivotFirstSubstitutionData`.
  This is intentional for the current assumption boundary.
- The row universe, actual Aoyagi strip predicate, and pivot-in-strip
  provenance are still external to the generic finite algebra.
- No chart construction, chart coverage, regularity, transition post-data,
  Jacobian formula, normal crossings, or RLCT extraction is proved.

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
