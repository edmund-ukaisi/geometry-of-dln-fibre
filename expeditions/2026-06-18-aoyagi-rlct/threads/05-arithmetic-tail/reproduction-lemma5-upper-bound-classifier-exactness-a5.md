# Reproduction - Lemma 5 upper-bound classifier exactness wrappers

Status: reproduced; Lean checked; source-boundary supplied.

## Source Boundary

Aoyagi PDF pp. 25-27 assert the Lemma 5 terminal order count through the
displayed branch families and interval count.  The current Lean
`terminalMinimumLabels` set is more explicit: it is a finite set of introduced
labels whose least value is zero and whose terminal exponent is the isolated
minimum numerator.  The source-backed bridge from each such Lean label back to
one of Aoyagi's displayed supplied branch labels is not reproduced.

Lean therefore keeps the no-extra direction as supplied data:

```text
UpperBoundClassifier C:
  for every label in C.terminalMinimumLabels,
  there exists x in C.fullBranches with C.branchLabel x = label.
```

This is equivalent to the containment

```text
C.terminalMinimumLabels subset C.branchLabelImage.
```

It is not constructed from the source in this slice.

## Finite-Set Calculation

Write

```text
B = C.fullBranches
f = C.branchLabel
I = C.branchLabelImage = B.image f
T = C.terminalMinimumLabels.
```

The existing easy direction gives

```text
I subset T.
```

This uses `a <= n+1` and the selected-width sum, because it says the supplied
branch labels attain the terminal minimum.

The supplied `UpperBoundClassifier C` gives

```text
T subset I.
```

Combining the two containments gives

```text
T = I.
```

If branch-label injectivity is also supplied,

```text
Set.InjOn f B,
```

then the same two containments give the bijection

```text
Set.BijOn f B T.
```

Maps-to is the easy inclusion `I subset T`, injectivity is the supplied
`Set.InjOn`, and surjectivity is the supplied classifier/no-extra inclusion.
Counting then gives

```text
T.card = I.card = B.card = a * (n + 1 - a) + 1.
```

The last equality is the existing supplied full-branch count, under
`a <= n+1`.

## Lean Targets

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_eq_branchLabelImage_of_upperBoundClassifier
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_iff_branchLabel_injOn_and_upperBoundClassifier
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_upperBoundClassifier_and_branchLabel_injOn
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_bijOn_terminalMinimumLabels_of_upperBoundClassifier
```

## Kill Conditions

- Dropping the supplied `UpperBoundClassifier` loses the no-extra containment.
- Dropping supplied branch-label injectivity loses the bijection and exact
  count wrappers.
- Replacing the bijection by a cardinal equality is too weak for later use:
  cardinal equality alone does not provide maps-to, injectivity, or
  surjectivity data.
- Treating these wrappers as a source proof of Lemma 5 upper-bound
  classification would overclaim.

## Nonclaims

No source construction of the upper-bound classifier, no branch-label
injectivity proof, no counted-datum back-to-label construction, no source
branch coverage, no pole order, no normal crossings, and no RLCT extraction is
proved here.
