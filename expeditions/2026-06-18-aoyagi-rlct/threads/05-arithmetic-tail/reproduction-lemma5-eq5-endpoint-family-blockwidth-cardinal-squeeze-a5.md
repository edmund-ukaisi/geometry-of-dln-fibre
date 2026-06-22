# Reproduction - Lemma 5 Eq5 endpoint-family block-width cardinal squeeze

Date: 2026-06-22.

Scope: a block-width variant of the endpoint-family terminal exactness and
cardinality wrappers.  This is still supplied finite bookkeeping; it does not
construct Aoyagi's Lemma 5 chart family or prove source-backed no-extra
coverage.

## Existing width-bound endpoint wrapper

The existing endpoint-family wrapper proves terminal-minimum exactness and

```text
TC.terminalMinimumLabels.card = a * (N + 1 - a) + 1
```

from the endpoint-family equality and the terminal cardinal-squeeze inputs,
including the per-label width hypothesis

```text
for label in TC.terminalMinimumLabels,
  selectedWidth(pOf label) <= width(label.1 + 1).
```

This per-label hypothesis is enough for the Eq5 own-block payload adapter, but
it is not the source-shaped width datum used elsewhere in the file.

## Block-width derivation

Assume instead the blockwise actual-width bound:

```text
for every selected block i and every source coordinate r in that block,
  selectedWidth(i) <= width(r).
```

The terminal payload hypotheses already include

```text
cut.block (pOf label) label.1
```

for every terminal-minimum label.  The existing cutpoint lemma

```text
cut.selectedWidthNat_le_actualWidth_of_block
```

therefore gives exactly the per-label width hypothesis required by the
width-bound endpoint wrapper:

```text
selectedWidth(pOf label) <= width(label.1 + 1).
```

After this conversion, all remaining inputs are passed unchanged to the
existing endpoint-family cardinal-squeeze theorem.

## Lean Targets

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze
```

## Nonclaims

- No Eq5 branch construction.
- No source production of endpoint records.
- No source-label legality.
- No proof of the endpoint-family equality from Aoyagi's source.
- No base-filter survival for source records.
- No source proof of terminal Eq5 payload coverage.
- No source proof of terminal `(p, alpha)` injectivity.
- No direct counted-datum back-to-label construction.
- No source-backed no-extra terminal-minimum coverage.
- No Lemma 5 order count, pole order, normal crossings, or RLCT extraction.
