# Review - A2 product-difference coordinate source data

Date: 2026-06-24.

Reviewers: controller self-check and xhigh `Descartes the 3rd`.

## Verdict

Passed after source-wording repair.

Descartes found no blocking issue in the Lean slice.  The Lean statements are
scoped correctly as finite source-coordinate and scalar-ideal bookkeeping:
combined index/value/ideal for the regular and residual scalar blocks,
equality to `fourMatrixEntryIdeal`, a source-stratum guarded neighborhood,
centered continuity, and endpoint count `H 1 * H(N+1)`.

## Repair

Descartes flagged one low source-fidelity issue in the reproduction note:
Aoyagi p. 13 literally displays the signed/corrected product-difference block

```text
C1 - Er,   -F2,   -F3,   prod_s C^(s) - F3 F2.
```

The signless/correction-free family is the cleaned ideal-level family obtained
from the earlier A2 entry-ideal boundary, not the literal printed display.
The reproduction and adjacent statement text were repaired to separate:

- the literal source display with signs and the lower-right `F3F2` correction;
- the already-proved entry-ideal cleanup; and
- this slice's combined scalar coordinate index for the cleaned four-family.

## Checks

The controller ran:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
lean/scripts/lb
lean/scripts/sorries
git diff --check
```

The focused module build and full library build passed.  The full build emitted
pre-existing Core linter warnings, but no errors.  `scripts/sorries` reported:

```text
0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

`git diff --check` passed.

## Nonclaims Checked

No exact-rank or source-rank openness, analytic coordinate chart,
regular-suspension chart construction, analytic germ-ideal transport, chart
coverage, transition regularity, Jacobian/prior compatibility, normal
crossings, pole order, or RLCT extraction is proved.
