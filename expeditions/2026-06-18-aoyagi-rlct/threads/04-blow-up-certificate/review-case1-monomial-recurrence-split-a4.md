# Review - A4 Case 1 monomial recurrence split

Status: reviewed; no blockers found.

## Reviewers

- Pen-and-paper scout: `Singer the 3rd`.
- Implementation reviewer: `Poincare the 3rd`.

## Math Review

The recurrence convention is

```text
monomialRec step (k+1) = step k * monomialRec step k.
```

Thus changing `step J` affects row `J+1` and later rows, but not rows
`i <= J`.  The implementation reviewer confirmed that `mulStepAt` changes
exactly one step level and that the bounds in the split lemmas match this
off-by-one convention.

The Case 1 strip comparison is correct: on `J+1 <= i <= h`, the old factor at
level `h` has not yet affected the source recurrence, while the new factor at
level `J` has affected the post recurrence.  Below the strip, `h+1 <= i`, both
recurrences rewrite to `u * monomialRec step i`.

## Lean/API Review

The statements are generic algebra over `[CommMonoid α]`.  They do not mention
Aoyagi labels, charts, supplied post-data, or source production.  The Case 1
names and comments identify the intended use without claiming a transition
theorem.

One minor API note: the hypothesis `J < h` in
`monomialRec_mulStepAt_case1_lower_eq` is a semantic guard for the Case 1
situation.  Algebraically the proof only needs `J+1 <= i`, but keeping the
guard makes the intended range explicit.

## Caveats

- This is not a chart-production theorem.
- It does not construct the factored-base recurrence state.
- It does not prove hidden old-label validity.
- It does not prove post-data production, Jacobian accounting, normal
  crossings, or RLCT extraction.

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
