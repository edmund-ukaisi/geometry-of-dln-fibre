# Reproduction - Lemma 5 terminal order formula bridge

Date: 2026-06-22.

Status: finite A5-to-A6 handoff under supplied obstruction hypotheses.

## Source Boundary

Aoyagi PDF pp. 25-27 supports the interval arithmetic and the intended order
shape, but the source audit confirms it does not supply the classifier,
branch-label injection, back-to-label map, terminal `tilde t=0`, or full
source construction needed for a source-backed Lemma 5 exactness theorem.

This slice therefore proves no new source-backed A5 theorem.  It only rewrites
the existing supplied finite obstruction in Aoyagi Theorem 2's final order
notation.

## Finite Calculation

Let

```text
data : AoyagiDefinition3CeilData (n+1) m
TC   : AoyagiLemma5SuppliedTerminalCandidateFamily
         ... n data.aParam data.ceilWidth m ...
```

The existing A5 obstruction equivalence says:

```text
TC.TerminalMinimumLabelExactness
  iff
    Set.InjOn TC.branchLabel TC.fullBranches
      and
    TC.terminalMinimumLabels.card <=
      data.aParam * (n + 1 - data.aParam) + 1.
```

Definition 3's order formula is definitionally

```text
data.theorem2OrderFormula =
  data.aParam * ((n+1) - data.aParam) + 1.
```

Thus the same obstruction can be stated in final-order notation:

```text
TC.TerminalMinimumLabelExactness
  iff
    Set.InjOn TC.branchLabel TC.fullBranches
      and
    TC.terminalMinimumLabels.card <= data.theorem2OrderFormula.
```

If the right-hand side is supplied, exactness follows.  The already-proved
terminal exactness count then gives

```text
TC.terminalMinimumLabels.card = data.theorem2OrderFormula.
```

## Lean Names

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_iff_branchLabel_injOn_and_theorem2OrderFormula_bound
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_card_bound_and_branchLabel_injOn
```

## Nonclaims

This does not construct branch-label injectivity, the terminal-minimum upper
bound, a source classifier, a back-to-label map, no-extra coverage, source
labels, chart coverage, pole order, normal crossings, or RLCT extraction.

## Kill Conditions

- Do not present the supplied upper bound as source-backed.
- Do not identify this terminal-count bridge with pole order; A6 still needs
  the finite exponent formula and A0 extraction boundary.
- Do not infer exactness without both branch-label injectivity and the
  terminal-minimum cardinal upper bound.
