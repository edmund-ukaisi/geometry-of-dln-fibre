# Review - Lemma 5 terminal exactness cardinal-bound equivalence

Status: reviewed/formalised; independent xhigh review survived.

## Scope

This slice adds a generic finite obstruction equivalence in
`Lemma5TerminalBridge.lean`.  It does not inspect or repair Aoyagi's printed
Eq3/Eq4/Eq5 families.

## Controller Check

The Lean statements are scoped correctly:

- the helper proves `terminalMinimumLabels = branchLabelImage` from the
  existing inclusion `branchLabelImage subset terminalMinimumLabels`, supplied
  branch-label injectivity, and a supplied numeric upper bound on
  `terminalMinimumLabels.card`;
- the `iff` theorem says `TerminalMinimumLabelExactness` is equivalent to
  supplied branch-label injectivity plus that supplied numeric upper bound,
  under `a <= n+1` and the selected-width sum.

No source-backed classifier, no-extra theorem, chart coverage theorem, pole
order theorem, normal-crossing theorem, or RLCT theorem is introduced.

## Checks

Focused Lean check passed:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean
```

Independent xhigh reviewer `Feynman` reported no blocking issues.  The
reviewer independently checked the new Lean lemmas as valid finite-cardinality
squeezes under the stated hypotheses, confirmed the reproduction note's
nonclaims were appropriately scoped, and reported both focused Lean and
`git diff --check` passing.

After the review, the theorem names were shortened to avoid a long-line style
warning; the theorem statements and proofs were unchanged.

Controller gate passed:

```text
cd lean && lake build DLNFibre.DLN.Aoyagi.Lemma5TerminalBridge
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reports `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build reports only pre-existing Core warnings.

## Nonclaims

This theorem does not prove the upper cardinal bound from Aoyagi's source.  It
does not construct branch-label injectivity, a terminal-minimum classifier, a
back-to-label map, source labels, source branches, pole order, normal
crossings, or RLCT extraction.
