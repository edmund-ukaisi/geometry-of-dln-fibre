# Review - A4 Case 2 source-current stack substitution block

Date: 2026-06-24.

Reviewer: xhigh subagent `Lagrange the 2nd`.

Verdict: pass.

## Scope

Reviewed the proposed theorem

```text
Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.
  continuing_sourceCurrentStack_suppliedCsucc_of_substitutionBlock_eq
```

in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

No files were edited by the reviewer.

## Findings

The theorem is source-boundary sound.  It is a pure consumer: it calls
`continuing_sourceCurrentStack_suppliedCsucc`, keeps the supplied `Csucc` from
`ob`, and rewrites only the lower-left substitution block by `hB`.

It does not construct `ob`, `Csucc`, suffixes, charts, transitions, analytic
normal-crossing data, pole order, or RLCT data.

The main type subtlety is that the parent theorem writes the block using the
displayed pivot value, while `hB` is stated with the outer selected variable
`u`.  This is acceptable because the existing simplification
`case2DisplayedSourceChartMap_pivot` identifies the displayed pivot value with
`u`.  The implemented proof uses the robust shape

```text
simpa [hB] using hq
```

rather than a brittle raw rewrite.

## Verification

Focused module build passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic
```
