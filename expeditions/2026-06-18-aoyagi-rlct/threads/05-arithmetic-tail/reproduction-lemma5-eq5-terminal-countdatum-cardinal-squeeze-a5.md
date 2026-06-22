# Reproduction - Lemma 5 Eq5 terminal counted-datum cardinal squeeze

Status: reproduced; Lean checked; supplied Eq5 classifier boundary composed
with finite cardinal squeeze.

## Source Boundary

The previous Eq5 terminal slice constructs
`TC.TerminalMinimumCountDatumClassifier` from supplied Eq5 own-block
common-domain payload data for every label already in
`TC.terminalMinimumLabels`.

This slice takes the finite consequences of that classifier.  It does not
prove the Eq5 payloads from Aoyagi's equations, the counted-datum classifier
injectivity, or branch-label injectivity.  The two injectivity hypotheses are
separate:

```text
Set.InjOn (label |-> some (pOf label, T label label.1))
  TC.terminalMinimumLabels
```

and

```text
Set.InjOn TC.branchLabel TC.fullBranches.
```

The first gives the upper bound through counted data.  The second is needed
only for exactness by cardinality squeeze.

## Calculation

Let

```text
T = TC.terminalMinimumLabels.
```

For every `label = (S,k)` in `T`, the supplied Eq5 payload classifier sends

```text
label |-> some (pOf label, T label S).
```

The Eq5 common-domain payload proves that this value lies in

```text
aoyagiLemma5CountDatumSet (N+1) a M m TC.family.baseValue.
```

The supplied counted-datum injectivity therefore gives a finite injection from
`T` into the counted-datum set.  The existing counted-datum cardinal theorem
then gives

```text
|T| <= a * (N + 1 - a) + 1.
```

The same argument applies after deriving the selected-width bound from
block-width, left-endpoint/minimum, off-selected dominance, or strict
off-selected dominance hypotheses.

For exactness, also let

```text
B = TC.fullBranches
f = TC.branchLabel
I = TC.branchLabelImage = B.image f
K = a * (N + 1 - a) + 1.
```

The existing supplied terminal-candidate bridge gives

```text
I subset T
```

from `a <= N+1` and the selected-width sum.  Supplied branch-label
injectivity gives

```text
|I| = |B| = K.
```

The Eq5 counted-datum classifier gives

```text
|T| <= K.
```

Hence `|T| <= |I|`.  Since `I subset T`, finite cardinality forces

```text
T = I.
```

Together with supplied branch-label injectivity, this is the existing
`TC.TerminalMinimumLabelExactness` package.  The exact terminal-minimum count
and the bijection

```text
Set.BijOn TC.branchLabel TC.fullBranches TC.terminalMinimumLabels
```

then follow from the existing exactness wrappers.

## Lean Targets

Upper-bound wrappers:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_eq5OwnBlockCommon_widthBound
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_eq5OwnBlockCommon_blockWidth
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_eq5OwnBlockCommon_leftEndpointMin
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_eq5OwnBlockCommon_offSelected
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_eq5OwnBlockCommon_offSelected_lt
```

Width-bound exactness wrappers:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_eq_branchLabelImage_of_eq5OwnBlockCommon_widthBound_cardSqueeze
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_cardSqueeze
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_cardSqueeze
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_bijOn_terminalMinimumLabels_of_eq5OwnBlockCommon_widthBound_cardSqueeze
```

## Kill Conditions

- Do not drop the Eq5 payload hypotheses for terminal-minimum labels.
- Do not drop the nonbase hypothesis.
- Do not conflate counted-datum injectivity with branch-label injectivity.
- Do not call the cardinal-squeeze equality a counted-datum-preserving
  back-to-label map.
- Do not infer an `UpperBoundClassifier` construction from Aoyagi's printed
  equations.

## Nonclaims

No Eq5 branch construction, no proof that every terminal-minimum label has
source-produced Eq5 data, no source-derived counted-datum injectivity, no
source-derived branch-label injectivity, no counted-datum-preserving
back-to-label map, no Lemma 5 order count from the printed branch families, no
pole order, no normal crossings, and no RLCT extraction is proved here.
