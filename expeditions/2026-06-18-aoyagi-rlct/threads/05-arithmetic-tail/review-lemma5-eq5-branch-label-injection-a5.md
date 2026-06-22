# Review - Lemma 5 Eq5 branch-label injection

Reviewer: xhigh Lean/API reviewer `Confucius`.

Verdict: pass.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`
- `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean`
- `reproduction-lemma5-eq5-branch-label-injection-a5.md`
- `statement-card-a5-lemma5-eq5-branch-label-injection.md`

## Findings

No findings.

## Lean/API Notes

The generic wrapper explicitly assumes nonbase branch-label injectivity and
base/nonbase separation.  The Eq5 specialization explicitly assumes
coordinatewise alpha injectivity, selected-block membership, the displayed Eq5
label formula, and base/nonbase separation.  The cross-coordinate step uses
source-coordinate equality plus `cut.block_index_unique`; the same-coordinate
step delegates to the existing fixed-coordinate alpha-indexed branch-label
injectivity theorem.

The review found no `Option` base-case gap, no cross-coordinate gap, and no
unadvertised source assumption.  The reproduction and statement card preserve
the intended nonclaims.

## Verification

The reviewer ran:

```text
git diff --check
source ~/.elan/env && lake env lean DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean
source ~/.elan/env && lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean
rg -n "sorry|axiom|native_decide|#exit" \
  lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean \
  lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean
```

All checks passed; the hygiene scan found no matches.
