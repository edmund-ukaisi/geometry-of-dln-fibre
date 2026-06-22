# Review - Lemma 5 Eq5 terminal counted-datum cardinal squeeze

Reviewer: xhigh Lean/API reviewer `Plato`.

Verdict: pass.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean`
- `reproduction-lemma5-eq5-terminal-countdatum-cardinal-squeeze-a5.md`
- `statement-card-a5-lemma5-eq5-terminal-countdatum-cardinal-squeeze.md`

## Findings

No findings.

## Lean/API Notes

The added wrappers are Lean/API-correct, match their stated contents, and stay
within the intended supplied-data boundary.  Counted-datum injectivity remains
a separate `hinj`/`hinjCountDatum` hypothesis passed into the counted-datum
classifier.  Branch-label injectivity remains a separate `hinjBranchLabel`
hypothesis used only by the finite cardinal-squeeze, exactness, and bijection
wrappers.

## Verification

The reviewer ran:

```text
git diff --check -- lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean
lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean
```

Both passed.

## Post-Rename Recheck

After the controller shortened the four width-bound exactness wrapper names to
the `_cardSqueeze` suffix, the reviewer re-checked the current diff.

Verdict: no findings.

The proof bodies still compose through the same counted-datum classifier and
existing cardinal-squeeze APIs.  Counted-datum injectivity remains separate
from branch-label injectivity.  The reproduction artifact, statement card,
`synthesis.md`, and `theorem-ledger.md` use the new names; targeted stale-name
searches for the old Eq5 `..._widthBound_and_branchLabel_injOn` form found no
matches.

The reviewer ran:

```text
git diff --check
lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean
```

Both passed.
