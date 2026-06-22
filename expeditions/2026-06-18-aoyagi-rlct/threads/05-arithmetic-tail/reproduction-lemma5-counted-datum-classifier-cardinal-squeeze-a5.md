# Reproduction - Lemma 5 counted-datum classifier cardinal squeeze

Status: reproduced; Lean checked; supplied classifier boundary.

## Source Boundary

Aoyagi's Lemma 5 upper-bound paragraph counts terminal candidates through
interval data, but the expedition has kept the map from Lean
`terminalMinimumLabels` to counted interval data as supplied classifier data.
This slice proves the finite consequence of that supplied classifier together
with supplied branch-label injectivity.  It does not construct the classifier
from the displayed equations.

## Calculation

Let

```text
B = C.fullBranches
f = C.branchLabel
I = C.branchLabelImage = B.image f
T = C.terminalMinimumLabels
N = a * (n + 1 - a) + 1.
```

Existing Lean facts give:

1. `I subset T`: supplied branch labels attain the terminal minimum, using
   `a <= n+1` and the selected-width sum.
2. `|B| = N`: the supplied full branch count.
3. If `Set.InjOn f B`, then `|I| = |B| = N`.
4. A supplied terminal-minimum counted-datum classifier gives `|T| <= N`.

Thus

```text
N = |I| <= |T| <= N.
```

So `|T| <= |I|`, and since `I subset T`, finite-set cardinality gives

```text
I = T.
```

Equivalently,

```text
T = I,
```

which supplies the no-extra field
`terminalMinimumLabels subset branchLabelImage`.  Together with supplied
branch-label injectivity, this is the existing
`TerminalMinimumLabelExactness` package.  The exact count and bijection then
follow from the existing exactness wrappers.

## Lean Targets

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_eq_branchLabelImage_of_countDatumClassifier_and_branchLabel_injOn
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_countDatumClassifier_and_branchLabel_injOn
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_countDatumClassifier_and_branchLabel_injOn
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_bijOn_terminalMinimumLabels_of_countDatumClassifier_and_branchLabel_injOn
```

## Kill Conditions

- Do not drop the supplied terminal-minimum counted-datum classifier.
- Do not drop supplied branch-label injectivity.
- Do not treat the cardinal squeeze as a constructed back-to-label map; it
  proves finite no-extra containment, not branch witnesses with counted-datum
  equality.
- Do not use this as a pole-order or RLCT statement.

## Nonclaims

No source construction of the counted-datum classifier, no branch-label
injectivity proof, no displayed Eq3/Eq4/Eq5 family construction, no
source-label legality, no terminal source realisation, no pole order, no
normal crossings, and no RLCT extraction is proved here.
