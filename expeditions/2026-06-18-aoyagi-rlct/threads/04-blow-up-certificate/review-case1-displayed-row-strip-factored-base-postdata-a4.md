# Review - A4 Case 1 displayed row-strip factored-base post-data

Status: reviewed; no blockers found.

## Reviewers

- Source scout: `Kuhn the 3rd`.
- Pen-and-paper scout: `Singer the 3rd`.
- Lean/API scout: `Arendt the 3rd`.

## Source And Math Review

The source scout checked Aoyagi PDF pp. 15-19.  The PDF explicitly factors
the old selected variable in Case 1(2) and displays
`b'_i = u_(S,J+1)b_i` over the residual row range.  It does not print a full
post-recurrence assignment for every old label.  Therefore the Lean boundary
must be supplied post-data relating a factored-old base state to a post state,
not a theorem that the original pre-state is preserved.

The pen-and-paper scout checked the recurrence convention.  A label at level
`r` first affects row weight `b_(r+1)`.  Hence the old selected factor at
level `J+J1` affects rows from `J+J1+1`, while the new label at level `J`
affects rows from `J+1`.  This validates the factored-base update

```text
post.weight i = u * factoredBase.weight i,   J+1 <= i,
```

and explains why strip rows get the selected factor from source entries while
lower rows get it from the factored old row weights.

## Lean/API Review

The Lean/API scout recommended a small checkpoint using a factored-old base
state and the existing recurrence post-data machinery.  The implementation
follows that recommendation:

- `Case1DisplayedRowStripFactoredBasePostData` is a naming alias, not a new
  source-production theorem.
- The row-strip pivot-first theorem uses `case1RowStripOldWeight` on the left
  and rewrites the right-hand diagonal to `post.weight`.
- The displayed `Q/P` wrapper chooses quotient witnesses from the factored-base
  monomial recurrence and rewrites the common `u` factor to post weights.

## Caveats

- The original pre-state to factored-base relation remains external.
- Hidden old-label source validity remains external.
- Complete post assignments for old labels are supplied, not extracted from
  the PDF.
- No chart coverage, regularity, Jacobian formula, normal crossings, or RLCT
  extraction is proved.

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
