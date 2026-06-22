# Review - A4 Case 2 Continuing Old-Top/Source-Suffix Stack

Reviewer: xhigh independent reviewer `Russell`.

## Verdict

No findings.  Bank as a supplied-boundary pivot-first stack identity.

## Checks

- The theorem is source-faithful to Aoyagi PDF pp. 20-21 at the finite
  matrix-algebra boundary: it keeps `C' = Q^-1 C`, uses the cleared `D'''`,
  lifts unchanged old top rows, and right-multiplies by the raw source suffix.
- The proof consumes the supplied paper `Q/P` equality, lifts it by
  `fromBlocks_mul_verticalBlock_eq_of_tail`, and then multiplies by
  `sourceSuffixProduct`.
- The result is not the lower-row theorem with `F := sourceSuffixProduct`: the
  lower-row theorem projects away old top rows and the pivot row, while this
  theorem preserves the old-top plus pivot-first `C'` stack.
- The phrase "actual source suffix" is acceptable because
  `sourceSuffixProduct` is the raw paper-order chain from `S+2` to `L`, while
  its entries remain supplied data.

## Nonclaims Checked

The theorem name and docs do not claim source production of a successor
`C'^(S+1)`, source production of the suffix, chart coverage, transition
invariance, normal crossings, pole order, termination, RLCT extraction, or
repair of the printed Case 2 vector mismatch.

## Verification

The reviewer ran:

```text
git diff --check
lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
```

Both passed when the Lean command was run from the `lean/` directory.  The
controller also ran the focused Lean check and the module build.
