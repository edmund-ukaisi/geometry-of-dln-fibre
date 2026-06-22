# Review - Lemma 5 Eq5 terminal alpha-injection cardinal squeeze

Reviewer: xhigh Lean/API reviewer `Jason`.

Verdict: pass.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean`
- `reproduction-lemma5-eq5-terminal-alpha-injection-cardinal-squeeze-a5.md`
- `statement-card-a5-lemma5-eq5-terminal-alpha-injection-cardinal-squeeze.md`
- the related expedition ledger edits

## Findings

No findings.

## Lean/API Notes

The two wrappers are thin compositions.  Counted-datum injectivity remains an
explicit `hinjCountDatum` hypothesis.  Terminal Eq5 payloads remain supplied
through `hT`, `hlabelBlock`, `hlabelFormula`, and `hlabel_ne_base`.  The branch
alpha map

```text
branchAlphaOf : β -> Nat
```

is separate from the terminal-label alpha map

```text
labelAlphaOf : (Sigma (fun _ : Nat => Nat)) -> Nat
```

The computed branch-label injectivity is passed only to the existing
cardinal-squeeze wrappers.  No Eq5-specific API was moved into the generic
terminal bridge.

The reproduction and statement card state conditional finite exactness and
preserve the nonclaims: no branch construction, alpha-domain coverage,
counted-datum injectivity, back-to-label coverage, pole order, normal
crossings, or RLCT extraction.

## Verification

The reviewer ran:

```text
git diff --check
lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean
rg -n "sorry|axiom|native_decide|#exit" \
  lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean
```

All checks passed; the hygiene scan found no matches.
