# Review - A4 Case 2 source-production obligation row-exhausted Cterm frontier

Date: 2026-06-22.

Reviewer: xhigh post-implementation reviewer `Halley the 2nd`.

## Verdict

Pass after documentation cleanup.

## Lean Scope Check

No Lean/source-fidelity issue was found with:

```text
RowExhaustedSourceSuffixSuppliedCtermPrefixPayload
SourceProductionObligation.rowExhausted_frontier_suppliedCtermPrefix
```

The theorem is a consumer-side rewrite.  It takes
`ob.rowExhausted_frontier hrow`, uses `ob.rowExhausted_Cterm_eq hrow`, and
rewrites only the terminal prefix factor to `Cterm.submatrix ...`.

## Boundary Check

The theorem does not construct `Cterm`, `Csucc`, suffixes, charts, coverage,
transition regularity, normal crossings, pole order, termination, or RLCT
data.  It also preserves the Aoyagi pp. 21-22 distinction between transported
`Q^-1 C` rows and original-row collapse only under stronger actual-width
hypotheses.

## Documentation Findings

The reviewer found stale next-chart-family wording in three historical A4
documents.  The current patch now marks those parts as superseded historical
API descriptions and removes the stale live-field wording.

## Checks

Focused Lean and module build passed.  Full-library build and final hygiene
checks are recorded in the statement card for this slice.
