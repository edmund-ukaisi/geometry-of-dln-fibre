# Statement card - A4 Case 1 monomial recurrence split

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`949cf88b23d4ba636cdd67fdf67dd2e464c0927d`.

Names:

- `DLNFibre.DLN.Aoyagi.mulStepAt`
- `DLNFibre.DLN.Aoyagi.mulStepAt_self`
- `DLNFibre.DLN.Aoyagi.mulStepAt_of_ne`
- `DLNFibre.DLN.Aoyagi.monomialRec_mulStepAt_eq_of_le`
- `DLNFibre.DLN.Aoyagi.monomialRec_mulStepAt_eq_mul_of_ge`
- `DLNFibre.DLN.Aoyagi.monomialRec_mulStepAt_case1_strip_split`
- `DLNFibre.DLN.Aoyagi.monomialRec_mulStepAt_case1_lower_eq`

## Statement

Lean now proves the off-by-one recurrence algebra for moving a single
monomial factor from an old selected level `h` down to a new level `J`.

With the recurrence convention

```text
b_(r+1) = step_r * b_r,
```

an extra factor inserted at level `r` affects rows from `r+1` onward and does
not affect rows up to `r`.

For Case 1(2), this gives:

```text
J+1 <= i <= h:
  old-source-at-h weight = base weight,
  new-post-at-J weight   = u * base weight;

h+1 <= i:
  old-source-at-h weight = new-post-at-J weight.
```

## Source Role

This supplies the elementary recurrence calculation behind the factored-base
Case 1(2) boundary.  It explains why the selected factor appears in the
row-strip source entries but in the lower residual row weights.

## Proved

- A reusable single-level step modification `mulStepAt`.
- Weights before or at the modified level are unchanged.
- Weights after the modified level are multiplied by the inserted factor.
- The Case 1 strip and lower-row recurrence comparisons follow.

## Not Proved

- No chart construction or chart coverage.
- No construction of the factored-base recurrence state.
- No source validity for the hidden old label.
- No post-data production theorem.
- No Jacobian, normal-crossing, or RLCT statement.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case1-monomial-recurrence-split-a4.md`.
- Review artifact:
  `review-case1-monomial-recurrence-split-a4.md`.

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
