# Review - Theorem 2 Terminal And Regular Sockets Source-Data Rank-Width Removal

Date: 2026-07-02.

Reviewer: xhigh independent reviewer `Meitner`.

## Verdict

PASS.  No required corrections.

## Lean Check

Reviewer verification passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean
lake env lean DLNFibre/DLN/Aoyagi/Theorem2Eq5TerminalOrderBridge.lean
lake env lean DLNFibre/DLN/Aoyagi/Theorem2RegularSuspensionFinalBridge.lean
git diff --check
```

Controller verification also passed focused module builds, warning-clean direct
elaboration for all three edited files, full local `DLNFibre` build,
`lean/scripts/sorries`, `git diff --check`, and direct axiom probes.  The new
declarations report only `[propext, Classical.choice, Quot.sound]`.

## Source And API Check

The reviewer confirmed that the current diff is source-safe and worth keeping:

- terminal counted-datum classifier wrappers for `L=2`;
- Eq5 endpoint payload wrappers for `L=2`;
- supplied regular-suspension chart-final wrappers for `L=2` and `ell=1`.

The wrappers remove a real source-range rank-width field by applying
`Ssrc.sourceRangeRankWidth_of_L_eq_two_sourceData` or
`S.sourceRangeRankWidth_of_ell_eq_one`.

## Scope Check

The reviewer specifically advised not to add lower-level `TC.*` `L=2`
variants, because those do not take rank-width, and not to add `ell=1`
terminal/Eq5 variants, because those APIs are shaped as `n+1`, making
`ell=1` an awkward `n=0` special socket rather than a natural field removal.

The reviewer found no branch choice, branch-independent formula, Eq5 payload
construction, regular-suspension certificate construction, normal-crossing
construction, or RLCT claim.
