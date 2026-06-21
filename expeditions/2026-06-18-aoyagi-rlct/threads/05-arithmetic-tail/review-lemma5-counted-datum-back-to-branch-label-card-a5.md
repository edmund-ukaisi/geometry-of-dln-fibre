# Review - Lemma 5 counted datum back-to-branch-label card bound

Date: 2026-06-21.

Reviewer: xhigh independent reviewer `Galileo`.

## Verdict

Pass.  No blocking Lean, mathematical, source-fidelity, naming, or bedrock
issue was found.

## Audit

The theorem

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_countDatumBackToBranchLabel
```

is correct finite bookkeeping.  It converts the supplied counted-datum
back-to-label bridge into the existing `UpperBoundClassifier`, then applies
the existing cardinal upper-bound theorem.

The hypotheses are scoped honestly.  The counted-datum classifier alone
already gives a numeric upper bound elsewhere, so the back-to-label hypothesis
is stronger than necessary for a bare inequality, but it matches this wrapper's
purpose: a direct consequence of the supplied back-to-label boundary.  The
statement does not require branch-label injectivity, exact cardinality, or a
source construction of the classifier, branch-coordinate map, or
back-to-label bridge.

The notes do not overclaim Aoyagi PDF pp. 26-27.  They describe those pages as
motivation for counted interval data and displayed branch formulas, while
keeping this slice as supplied finite bookkeeping.

## Verification

The reviewer reported:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean
git diff --check
```

and a forbidden-token scan on the touched Lean file passing.  The controller
also ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean
lake build DLNFibre.DLN.Aoyagi.Lemma5TerminalBridge
lake build DLNFibre
./scripts/sorries
git diff --check
```

with the build and scanner passing; the full build emitted only pre-existing
Core linter warnings.
