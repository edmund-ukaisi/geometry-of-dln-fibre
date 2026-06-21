# Reproduction - Lemma 5 counted-datum back-to-label bijection

Status: reproduced; Lean checked; independent xhigh review survived.

## Source

Aoyagi PDF pp. 25-27 gives the Lemma 5 count and the displayed families for
the lower-bound side.  The upper-bound paragraph counts possible interval
data, but it does not spell out a Lean-level classifier from terminal-minimum
labels, nor an injection or a back-to-label construction.

This slice is therefore a supplied-boundary wrapper.  It starts only after a
counted-datum classifier, a back-to-label bridge, and branch-label injectivity
have all been supplied.

## Calculation

Let `C` be a supplied terminal-candidate family.  The existing supplied
exactness package has two fields:

```text
Set.InjOn C.branchLabel C.fullBranches
C.terminalMinimumLabels subset C.branchLabelImage
```

The existing back-to-label bridge supplies the second field: for every
terminal-minimum label, it gives a supplied branch whose branch label is that
terminal-minimum label.  Together with supplied branch-label injectivity, this
builds `TerminalMinimumLabelExactness`.

The existing exactness-to-bijection theorem then gives

```text
Set.BijOn C.branchLabel C.fullBranches C.terminalMinimumLabels.
```

The selected-width sum and `a <= n+1` enter only through the easy direction
that supplied branch labels are terminal-minimum labels.

## Lean Target

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_bijOn_terminalMinimumLabels_of_countDatumBackToBranchLabel
```

## Kill Conditions

- Dropping supplied branch-label injectivity kills injectivity of the bijection.
- Dropping the supplied back-to-label bridge leaves no no-extra containment.
- Dropping the counted-datum classifier invalidates the back-to-label bridge
  hypothesis itself.
- Dropping the selected-width sum or `a <= n+1` kills the existing easy
  branch-label-to-terminal-minimum direction.

## Nonclaims

No counted-datum classifier is constructed from Aoyagi's printed equations.
No back-to-label map, branch-label injectivity, source labels, source branch
family, terminal source realisation, pole order, normal crossings, or RLCT
extraction is proved.
