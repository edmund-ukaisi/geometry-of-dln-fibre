# Review - A2 regular-suspension coordinate index

Date: 2026-06-24.

Reviewer: controller self-check and independent xhigh `Russell the 3rd`.

## Verdict

Passed after one import-boundary repair.

The coordinate index is finite bookkeeping for the three p. 13 regular block
families only.  The residual block `S.D` is not included.  The abstract
cardinality theorem keeps endpoint-cardinality identifications explicit, and
the endpoint-compatible theorem derives the fixed-base endpoint counts from the
through-subspace complement construction, the base product-rank equality, and
the dimension convention.

The local-certificate projection consumes only the existing
`coefficientFields_centered_continuous` field and projects the first three
block fields componentwise.  It does not use or strengthen the source-rank
neighborhood field.

Russell's xhigh review found no source-fidelity overclaim in the theorem
statements or docs.  The one issue was a dependency leak: the first version
imported `RegularSuspensionInterface`, coupling this coordinate slice to the
supplied `Cfull`/regular-suspension boundary.  The file now imports only
`ProductReductionEntryIdealBoundary` and `FinalFormula`.

## Build Check

```text
cd lean
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
lake build DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
lake env lean DLNFibre.lean
```

These focused checks passed after the endpoint-count strengthening and import
repair.  The broader `lean/scripts/sorries` and `git diff --check` gates should
still be run before banking the current dirty expedition stack.
