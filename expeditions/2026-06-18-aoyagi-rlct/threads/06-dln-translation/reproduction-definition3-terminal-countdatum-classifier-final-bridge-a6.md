# Reproduction - Definition 3 terminal counted-datum classifier final bridge

Status: finite source-data handoff; formalisation-ready.

This slice is not a new proof of Aoyagi Lemma 5.  The counted-datum set,
terminal counted-datum classifier, and branch-label exactness interfaces are
already formalised in the A5 files.  The remaining small A6 handoff is to
combine those supplied finite objects with Definition 3 source-data provenance,
so the final Theorem 2 socket can be filled for the `m,data` produced from the
same selected cutpoints.

## Inputs

Fix:

```text
Ssrc : AoyagiDefinition3SourceData L (n+1) H r C
hr   : for 1 <= s <= L+1, r <= H s.
```

The existing Definition 3 source-data theorem gives selected reduced widths and
ceiling data:

```text
exists m data,
  m = aoyagiSelectedReducedWidths H r C
  and Definition 3 side conditions for m,data.
```

For each produced `m,data`, assume a supplied terminal classifier payload:

```text
TC : AoyagiLemma5SuppliedTerminalCandidateFamily ...
classifier : TC.TerminalMinimumCountDatumClassifier
hinj : Set.InjOn TC.branchLabel TC.fullBranches
```

and supplied A0 finite certificates:

```text
p in activePairs,
ratioAt p = theorem2 lambda from data,
all active ratios are >= that value,
one displayed-ratio chart count equals TC.terminalMinimumLabels.card,
all displayed-ratio chart counts are <= that card.
```

## Calculation

The existing counted-datum classifier bridge proves:

```text
TC.terminalMinimumLabels.card <= data.theorem2OrderFormula.
```

Together with `hinj`, the terminal-cardinality squeeze proves:

```text
TC.terminalMinimumLabels.card = data.theorem2OrderFormula.
```

The supplied active-pair data gives:

```text
D.exponentMinimum = aoyagiTheorem2Lambda_fromCeilData L (n+1) H r m data.
```

The supplied displayed-ratio chart count and chart-count upper bound convert to
the exponent-order equality:

```text
D.exponentOrder = TC.terminalMinimumLabels.card.
```

Composing these two equalities gives the finite exponent formula hypothesis for
the produced `m,data`.  Adding the existing normal-crossing extraction
hypothesis fills `AoyagiTheorem2SuppliedFinalBoundary`.

The chart-certificate version is the same argument with
`Cnc.exponentData` in place of `D` and `Cnc.ExtractionHypothesis` in place of
the raw extraction hypothesis.

## Nonclaims

- No counted-datum classifier is constructed from Aoyagi's equations.
- No branch-label injectivity is proved from source.
- No back-to-label map, Eq3/Eq4/Eq5 family, or Lemma 5 exactness is proved.
- No active-ratio bound, chart-count theorem, chart production, or
  pole-order/RLCT consequence independent of the supplied A0 extraction
  hypothesis is proved.
