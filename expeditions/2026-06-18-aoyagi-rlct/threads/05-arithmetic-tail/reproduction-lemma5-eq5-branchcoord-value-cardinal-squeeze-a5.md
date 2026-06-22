# Reproduction - Lemma 5 Eq5 branch-coordinate/value cardinal squeeze

Date: 2026-06-22.

Scope: finite branch-label injectivity and terminal cardinal-squeeze packaging
from supplied branch-coordinate left-endpoint labels and supplied branch-value
labels.  This is a hypothesis-reduction layer over the preceding value-label
branch-injection slice.  It does not construct Eq5 branches, prove the
branch-coordinate map from source, prove source-label legality, prove terminal
Eq5 payload coverage, prove source-backed no-extra coverage, prove a Lemma 5
order count, prove pole order, prove normal crossings, or extract RLCT data.

## Selected-Block Membership

Let `TC` be a supplied terminal-candidate family and let `cut` be selected
cutpoints for `N+1` selected intervals.  Suppose a supplied coordinate map
records that every nonbase branch in the `j`th branch family has coordinate
`j`:

```text
branchCoord b = j
```

for `b in TC.family.branches j`, and suppose the source coordinate of the
terminal branch label is the left endpoint of that recorded coordinate:

```text
TC.branchS (some b) = cut.point (branchCoord b) - 1.
```

If `j in Icc 1 N`, then `j < N+1`, so the cutpoint API gives:

```text
cut.block j (cut.point j - 1).
```

Substituting `branchCoord b = j` into the supplied source-coordinate formula
and unfolding `TC.branchLabel` gives:

```text
cut.block j (TC.branchLabel (some b)).1.
```

This proves the `hbranchBlock` input needed by the branch-label injection
adapters.  It is not a proof that the branch-coordinate map or the branch label
is source-produced.

## Value-Label Relation

The value-label injection theorem needs:

```text
TC.family.value b = ((TC.branchLabel (some b)).2 : Z) - 1.
```

Since `TC.branchLabel x = (TC.branchS x, TC.branchK x)` by definition, this
follows from the supplied branch-value label relation:

```text
TC.family.value b = (TC.branchK (some b) : Z) - 1.
```

This is only a definitional adapter; the branch-value label relation itself is
still supplied.

## Cardinal Squeeze

The combined branch-injection wrapper feeds the two derived inputs into:

```text
TC.branchLabel_injOn_of_nonbase_valueLabel_terminalEndpointBase
```

using the explicit terminal-endpoint base label to separate the base branch.
The terminal exactness and count wrappers then feed this branch-label
injectivity into the existing pAlpha/value-label finite cardinal squeeze:

```text
TC.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_valueLabel_cardSqueeze
TC.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_pAlpha_valueLabel_cardSqueeze
```

Therefore, under supplied terminal Eq5 payloads, supplied terminal
`(p, alpha)` injectivity, supplied branch-coordinate data, supplied
left-endpoint source labels, supplied branch-value labels, terminal-label
nonbase inequalities, and the terminal-endpoint base label, Lean proves:

```text
TC.TerminalMinimumLabelExactness
TC.terminalMinimumLabels.card = a * (N+1-a) + 1.
```

This remains a conditional terminal-candidate exactness theorem.  It is not a
source-backed no-extra coverage theorem and it is not Aoyagi Lemma 5's
source chart-family order count.

## Lean Targets

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.branchBlock_of_branchCoord_leftEndpoint
AoyagiLemma5SuppliedTerminalCandidateFamily.valueLabel_of_branchK_value
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_branchCoord_leftEndpoint_branchK_value_terminalEndpointBase
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_branchCoordVal_cardSqueeze
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_pAlpha_branchCoordVal_cardSqueeze
```

## Nonclaims

- No Eq5 branch construction.
- No source proof of branch-coordinate correctness.
- No source proof of branch source-label or value-label formulas.
- No source proof of terminal Eq5 payload coverage.
- No source proof of terminal `(p, alpha)` injectivity.
- No direct counted-datum back-to-label construction.
- No source-backed no-extra terminal-minimum coverage.
- No Lemma 5 order count, pole order, normal crossings, or RLCT extraction.
