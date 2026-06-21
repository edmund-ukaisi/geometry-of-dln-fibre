# Review - Lemma 5 terminal exactness/bijection equivalence

Status: reviewed/formalised; independent xhigh review survived.

## Scope

This slice packages two existing finite supplied-boundary wrappers into an
`iff` between `TerminalMinimumLabelExactness` and `Set.BijOn C.branchLabel
C.fullBranches C.terminalMinimumLabels`.

## Verdict

No findings.  The theorem is finite API bookkeeping and keeps the
selected-width sum and `a <= n+1` visible on the forward direction.
Independent xhigh reviewer `Epicurus` found no blocking issue.

## Checks

Focused Lean check passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean
```

Independent xhigh reviewer `Epicurus` checked the declaration signature,
focused Lean build, streamed `#check/#print axioms`, and target-file no-sorry
scan.  The reviewer reported only ordinary classical/quotient axioms
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## Nonclaims

This theorem does not construct exactness, a classifier, a back-to-label map,
branch-label injectivity, source labels, source branches, pole order, normal
crossings, or RLCT extraction from Aoyagi's source.
