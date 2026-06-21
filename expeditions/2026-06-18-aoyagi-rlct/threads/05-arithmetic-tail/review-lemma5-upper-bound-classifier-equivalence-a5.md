# Review - Lemma 5 upper-bound classifier equivalence

Reviewer: Nietzsche, xhigh-effort subagent.
Date: 2026-06-21.

## Scope

- `lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`
- `reproduction-lemma5-upper-bound-classifier-interface-a5.md`
- `statement-card-a5-lemma5-upper-bound-classifier-interface.md`
- associated ledger updates

## Findings

None.

## Verdict

Pass.  The Lean equivalence is exact, and the documentation is scoped to
supplied finite bookkeeping.

`branchLabelImage` is the image of `C.fullBranches` under `C.branchLabel`, and
`UpperBoundClassifier` is exactly the witness form of membership in that image
for each element of `terminalMinimumLabels`.  The reverse theorem and iff are
just finite-image unpacking.

No overclaiming was found.  The documents exclude a source-backed classifier,
label-to-vector and minimum-to-lambda bridges, Case 1(2) uniqueness,
branch-label injectivity, back-to-label coverage, pole order, normal crossings,
and RLCT extraction.

## Verification

The reviewer typechecked:

```bash
cd /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean
lake env lean DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean
```
