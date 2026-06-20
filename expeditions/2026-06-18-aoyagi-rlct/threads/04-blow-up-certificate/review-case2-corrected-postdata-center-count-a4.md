# Review - A4 Case 2 Corrected Post-Data Center Count

Status: post-Lean xhigh review passed.

## Reviewers

Pre-Lean/read-only scouts:

- xhigh source/math scout `Pasteur the 4th`.
- xhigh Lean/API scout `Meitner the 4th`.

Post-Lean reviewers:

- xhigh Lean/API reviewer `Linnaeus the 4th`.
- xhigh source/docs reviewer `Noether the 4th`.

## Source and Math Review

The source/math scout approved this checkpoint only as a thin supplied
bookkeeping projection. The pen-and-paper content is:

```text
numerator'_(S,J+1) = (M(S)-J)(M^(S+1)-J)
                   = |{J+1..M(S)} x {J+1..M^(S+1)}|.
```

The scout emphasized that this does not show the chart produces the post-data
and does not compute a Jacobian exponent.

## Lean and API Review

The Lean/API scout supplied checked snippets for the generic
`Case2CorrectedExponentPostData` projection and the displayed supplied-boundary
projection. Lean now includes the generic projection plus both source-selected
and displayed boundary projections.

Post-Lean Lean/API review found no blocking or nonblocking issues in the new
theorem statements. The reviewer checked namespace placement, hypotheses,
coercions, and the fact that the statements only project supplied post-data.
The reviewer also reran the focused Lean check, diff check, and forbidden-token
scan over Aoyagi Lean files.

Post-Lean source/docs review found no blocking issues. The only low finding was
that this review artifact still said post-Lean review was pending; this update
resolves it. The reviewer confirmed that the docs keep prefix-minimum rows
separate from actual-width columns and do not claim chart production,
Jacobian/volume arithmetic, coverage, RLCT extraction, transition invariance,
termination, or repair of the printed-vector mismatch.

## Required Caveats

- This uses corrected prefix-minimum post-data, not the PDF's printed
  actual-width vector.
- This is supplied exponent bookkeeping, not chart production.
- This is not a Jacobian exponent.
- The equality to an integer cardinality uses bounds from displayed
  continuation.

## Verification

Pre-review focused Lean check:

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Post-Lean reviewer checks:

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `git diff --check -- lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- forbidden-token scan over `lean/DLNFibre/DLN/Aoyagi`
