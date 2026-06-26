# Review - Lemma 5 Eq5 endpoint first-nonbase upper bound

Reviewer: xhigh Lean/API and source-fidelity reviewer `Copernicus the 3rd`.

Verdict: pass after documentation fix.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean`
- `reproduction-lemma5-terminal-minimum-counted-datum-classifier-source-attempt-a5.md`
- `statement-card-a5-lemma5-eq5-endpoint-first-nonbase-upper-bound.md`
- related thread, synthesis, priorities, claim, and theorem-ledger updates.

## Finding

Low documentation issue, fixed: the statement-card verification command was
cwd-sensitive.  It now explicitly runs through `cd lean && ...`.

No mathematical/source overclaiming or Lean API blocking issue was found.  The
theorem remains a conditional upper bound from explicit Eq5 endpoint-chain
data plus supplied injectivity of the deterministic first-nonbase selector.
The artifacts do not claim source construction of the full terminal classifier,
selector injectivity, no-extra coverage, exactness, pole order, normal
crossings, or RLCT.

## Verification

The controller ran:

```text
git diff --check
```

```text
cd lean && scripts/sorries
```

```text
cd lean && env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.Lemma5Eq5TerminalClassifier
```

The reviewer independently reported:

```text
git diff --check
```

```text
cd lean && env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.Lemma5Eq5TerminalClassifier
```

```text
rg -n "\bsorry\b|\badmit\b|\baxiom\b|\bunsafe\b|native_decide|#exit" lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean
```

All passed; the search found no matches.
