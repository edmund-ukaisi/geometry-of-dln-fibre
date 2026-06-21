# Reproduction - Lemma 5 terminal exactness/bijection equivalence

Status: reproduced; Lean checked; independent xhigh review survived.

## Source

Aoyagi PDF pp. 25-27 counts terminal-minimum branches but does not give a
Lean-level exactness package or branch-label bijection.  In this expedition,
both are supplied-boundary interfaces:

- `TerminalMinimumLabelExactness` packages branch-label injectivity and
  no-extra containment;
- `Set.BijOn C.branchLabel C.fullBranches C.terminalMinimumLabels` packages
  the same finite data as a bijection.

This slice proves only that the two supplied-boundary formulations are
equivalent once the supplied branches are known to attain the minimum.

## Calculation

The forward direction is already proved:

```text
TerminalMinimumLabelExactness
  -> Set.BijOn branchLabel fullBranches terminalMinimumLabels.
```

It uses `a <= n+1` and the selected-width sum to prove the easy containment
from supplied branch labels into `terminalMinimumLabels`.

The reverse direction is also already proved:

```text
Set.BijOn branchLabel fullBranches terminalMinimumLabels
  -> TerminalMinimumLabelExactness.
```

The new theorem packages these two directions as an `iff`.

## Lean Target

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_iff_branchLabel_bijOn
```

## Kill Conditions

- Dropping `a <= n+1` or the selected-width sum breaks the forward direction
  because supplied branch labels are no longer known to be terminal-minimum
  labels.
- Replacing `Set.BijOn` by a cardinal equality is too weak: the reverse
  direction needs actual maps-to, injection, and surjection fields.
- Treating the equivalence as source construction would overclaim; both sides
  remain supplied-boundary data.

## Nonclaims

No source exactness, no no-extra classifier, no back-to-label map, no
branch-label injectivity, no source labels, no source branch construction, no
pole order, no normal crossings, and no RLCT extraction is proved.
