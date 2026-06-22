# Reproduction - Lemma 5 Eq5 terminal alpha-injection cardinal squeeze

Status: reproduced; Lean checked; xhigh review passed.

## Source Boundary

The previous terminal counted-datum cardinal-squeeze slice proved exactness
from two independent supplied injectivity hypotheses:

```text
Set.InjOn countedDatum TC.terminalMinimumLabels
Set.InjOn TC.branchLabel TC.fullBranches
```

The previous branch-label injection slice replaced the second hypothesis by
explicit Eq5 alpha-indexed branch data:

```text
coordinatewise alpha injectivity,
selected-block membership for nonbase branch labels,
the Eq5 displayed branch-label formula,
base/nonbase branch-label separation.
```

This slice composes those two APIs.  It is still a conditional finite
cardinality squeeze.  It does not prove counted-datum injectivity, construct
Eq5 branches, or prove no-extra terminal-minimum coverage from Aoyagi's
printed paragraph.

## Reproduction

Let `TC` be a supplied terminal-candidate family and let

```text
Tmin = TC.terminalMinimumLabels
B = TC.fullBranches
I = TC.branchLabelImage.
```

The Eq5 terminal counted-datum classifier, under supplied terminal-label
payloads and counted-datum injectivity, gives:

```text
|Tmin| <= a * (N + 1 - a) + 1.
```

The supplied terminal-candidate lower-bound package gives:

```text
I subset Tmin.
```

The supplied family has exactly

```text
|B| = a * (N + 1 - a) + 1.
```

The new Eq5 alpha-indexed branch-label injection theorem proves

```text
Set.InjOn TC.branchLabel B
```

from the explicit nonbase branch hypotheses.  Hence

```text
|I| = |B| = a * (N + 1 - a) + 1.
```

Since `I subset Tmin` and `|Tmin| <= |I|`, finite cardinality forces

```text
Tmin = I.
```

Together with branch-label injectivity, this is
`TC.TerminalMinimumLabelExactness`.  The existing exact-count wrapper then
gives

```text
TC.terminalMinimumLabels.card = a * (N + 1 - a) + 1.
```

## Lean Targets

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_alphaIndexedBranch_cardSqueeze
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_alphaIndexedBranch_cardSqueeze
```

## Kill Conditions

- Do not drop counted-datum injectivity.  The alpha-indexed branch theorem
  proves only branch-label injectivity.
- Do not identify the terminal-label alpha map with the branch alpha map; they
  have different domains.
- Do not replace terminal-label block membership with nonbase branch block
  membership, or conversely.
- Do not infer base/nonbase branch-label separation from `none` and `some`
  being different tags; their Sigma labels can coincide.
- Do not treat the cardinal squeeze as a counted-datum-preserving
  back-to-label map.

## Nonclaims

No Eq5 branch construction, no alpha-domain coverage, no source production of
terminal Eq5 payloads, no counted-datum injectivity, no counted-datum
back-to-label map, no `UpperBoundClassifier` construction from source,
no-extra terminal-minimum coverage, no Lemma 5 order count from Aoyagi's
printed branch families, no pole order, no normal crossings, and no RLCT
extraction is proved here.
