# Review - selected-entry local finite exponent minimum and order

Date: 2026-06-23.

Reviewer: xhigh fidelity/bedrock reviewer `Erdos the 2nd`.

Status: passed.

## Scope

Reviewed:

- the added finite exponent theorem block in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`;
- `reproduction-selected-entry-local-exponent-min-order-a4.md`;
- `statement-card-a4-selected-entry-local-exponent-min-order.md`.

The review checked the finite ratio `(h+1)/(2k)`, the use of
`Finset.card_erase_add_one`, the local finite exponent-minimum proof, the
local finite exponent-order proof, and whether the docs overclaim global A0
or RLCT conclusions.

## Findings

No high, medium, or low formalisation or mathematical inaccuracies were found.

The ratio computation is faithful to the finite normal-crossing exponent
interface: the unique coordinate has `k = 1`,
`h = card(center.erase pivot)`, and `Finset.card_erase_add_one pivot.2`
proves `h + 1 = center.card`.  Therefore the local ratio is
`center.card / 2`.

The local exponent-minimum proof is valid for this one-chart,
one-coordinate certificate.  The coordinate is active because `lossExp = 1`,
and `fin_cases` exhausts all possible active chart-coordinate pairs.

The local exponent-order proof is sound.  Every chart count is bounded by `1`
because the coordinate type is `Fin 1`, and positivity follows from the
finite exponent interface's active-minimum attainment theorem.

The reproduction and statement card keep the boundary local and explicitly
deny global A0 chart-family, global active-ratio lower-bound, global
chart-count/order, pole-order, and RLCT conclusions.

## Residual Risk

The existing bridge type name `Case2DisplayedContinuingA0ExponentCoordinateBridge`
remains stronger than its fields and can be instantiated for this local
microcertificate's own exponent data.  This is not a flaw in the reviewed
slice, but a future API split should reserve the A0 name for actual global A0
data and put the generic exponent-coordinate bridge under a non-A0 name.

## Verification

Reviewer ran:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
```

Controller also ran:

```text
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

All checks passed.  The full aggregator build emitted only unrelated
pre-existing Core linter warnings.
