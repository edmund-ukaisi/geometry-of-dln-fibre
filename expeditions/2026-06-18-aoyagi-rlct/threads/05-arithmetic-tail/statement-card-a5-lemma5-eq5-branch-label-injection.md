# Statement card - A5 Lemma 5 Eq5 branch-label injection

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_fullBranches_of_some_injOn`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_eq5AlphaIndexed_nonbase`

## Claim

Full supplied terminal branch-label injectivity follows from injectivity on
nonbase branches plus explicit separation of the base branch label from every
nonbase branch label.

For Eq5 alpha-indexed nonbase branches, the nonbase injectivity follows
coordinatewise from supplied alpha injectivity, supplied selected-block
membership of the source coordinate, and the displayed Eq5 label formula.

## Proved

The generic `Option` wrapper handles the base/nonbase cases and delegates the
`some`/`some` case to a supplied nonbase injection.

The Eq5 specialization recovers the source coordinate for each nonbase branch,
uses selected-cutpoint block uniqueness to put two equal labels in the same
coordinate family, and then invokes the existing fixed-coordinate
alpha-indexed branch-label injection theorem.

## Assumed

The supplied terminal-candidate family, the selected cutpoints, the
coordinatewise branch families, supplied coordinatewise alpha injectivity,
supplied block membership for the source coordinate of every nonbase branch,
the supplied Eq5 label formula, and explicit base/nonbase branch-label
separation.

## Deferred

Eq5 branch construction, alpha-domain coverage, source production of terminal
payloads, counted-datum injectivity, back-to-label coverage, upper-bound
classifier construction, no-extra terminal-minimum coverage, Lemma 5 order
count, pole order, normal crossings, and RLCT extraction.

## Verification

Focused Lean checks:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean
lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean
```

## Review

xhigh reviewer `Confucius` passed; see
`review-lemma5-eq5-branch-label-injection-a5.md`.
