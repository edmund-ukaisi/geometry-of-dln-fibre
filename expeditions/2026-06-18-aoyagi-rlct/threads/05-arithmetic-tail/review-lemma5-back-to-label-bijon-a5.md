# Review - Lemma 5 counted-datum back-to-label bijection

Status: reviewed/formalised; independent xhigh review survived.

## Scope

This slice is a supplied-boundary API wrapper.  It proves that existing
supplied counted-datum back-to-label data and supplied branch-label injectivity
give the standard `Set.BijOn` form of terminal-minimum exactness.

## Verdict

No findings.  The theorem is a one-line composition of existing
supplied-boundary theorems and does not claim that Aoyagi's printed Lemma 5
paragraph constructs the classifier, the back-to-label bridge, or injectivity.
Independent xhigh reviewer `Archimedes` found no blocking issue.

## Checks

Focused Lean check passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean
```

xhigh source scout `Nietzsche` and xhigh pen-and-paper scout `Russell`
independently found no source-backed no-extra/classifier bridge in Aoyagi
pp. 25-27.  xhigh Lean API scout `Hegel` proposed this exact supplied-boundary
wrapper and reported that it typechecked.

Independent xhigh reviewer `Archimedes` checked the target signature, focused
Lean build, target-file axiom report, target-file no-sorry scan, and import
scope.  The reviewer found only ordinary classical/quotient axioms
`propext`, `Classical.choice`, and `Quot.sound`, and no quiver input.

## Nonclaims

This theorem does not construct source branches, source labels, a
counted-datum classifier, a back-to-label map, or branch-label injectivity from
Aoyagi's printed equations.  It does not prove terminal source realisation,
Lemma 5 source exactness, pole order, normal crossings, or RLCT extraction.
