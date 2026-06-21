# Reproduction - Lemma 5 counted datum back-to-branch-label boundary

Status: supplied back-to-label boundary; formalisation-ready as finite
bookkeeping.

Aoyagi's upper-bound paragraph suggests a route from terminal candidates to
counted interval data and then back to the displayed branch family.  The first
part is represented in Lean by a supplied counted-datum classifier on
`terminalMinimumLabels`.  The missing second part is the back-to-label bridge:
the counted datum assigned to a terminal label should identify a supplied
branch whose branch label is the original terminal label.

## Supplied bridge

Fix:

```text
C : AoyagiLemma5SuppliedTerminalCandidateFamily ...
classifier : C.TerminalMinimumCountDatumClassifier
branchCoord : beta -> Nat
```

The branch coordinate function lets a supplied branch carry its own counted
datum:

```text
none      |-> none
some b    |-> some (branchCoord b, C.family.value b).
```

A supplied back-to-label bridge says that for every

```text
label in C.terminalMinimumLabels,
```

there exists

```text
x in C.fullBranches
```

such that

```text
C.branchLabel x = label
```

and the counted datum attached to `x` is the same as `classifier.classify
label`.

## Consequence

The branch-label equality alone gives the existing supplied
`UpperBoundClassifier`: for every terminal-minimum label, there is a supplied
branch with that label.  Equivalently, the bridge gives the no-extra inclusion

```text
C.terminalMinimumLabels subset C.branchLabelImage.
```

The counted-datum equality is retained in the supplied bridge because it is
the intended route through Aoyagi's interval-count paragraph; the final
finite-set consequence uses only the branch-label witness.

## Nonclaims

- No counted-datum classifier is constructed from Aoyagi's source.
- No branch coordinate map is constructed.
- No back-to-label bridge is proved from equations `(3)`, `(4)`, or `(5)`.
- No branch-label injectivity is proved.
- No source-label legality, terminal branch construction, pole order, normal
  crossings, or RLCT extraction is proved.
