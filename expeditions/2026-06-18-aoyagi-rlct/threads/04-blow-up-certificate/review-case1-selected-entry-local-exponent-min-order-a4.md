# Review - Case 1 selected-entry local exponent minimum and order

Date: 2026-06-23.

Reviewer: xhigh final reviewer `Lagrange`.

Status: passed after artifact-link fix.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`;
- `reproduction-case1-selected-entry-local-exponent-min-order-a4.md`;
- `statement-card-a4-case1-selected-entry-local-exponent-min-order.md`;
- the A4 entries in `priorities.md`, `claims.md`, `theorem-ledger.md`, and
  `threads/04-blow-up-certificate/thread.md`.

The review checked Lean statement correctness, proof reuse, source fidelity to
Aoyagi PDF p. 6 and pp. 16-17, and overclaiming boundaries.

## Findings

No mathematical or Lean blockers were found.

The Lean statements are correctly local to the selected-entry
microcertificates.  The ratio and finite-minimum wrappers reuse the generic
selected-entry `center.card / 2` theorems and rewrite the Case 1 center
cardinality to the full

```text
1 + J1 * (n(S+1)-J),
```

not just the erased-center/formal-Jacobian exponent.

The source and pen-and-paper boundary is faithful: Aoyagi PDF p. 6 supplies the
finite `(h_j+1)/(2 k_j)` reading, while PDF pp. 16-17 supply the Case 1 center,
the two selected charts, and the formal increment
`J1 * (M^(S+1)-J)`.  The docs consistently keep the result finite-local and do
not claim analytic Jacobian control, chart coverage, global A0
minimum/order, pole order, or RLCT extraction.

## Incorporated Fix

The reviewer found a broken documentation reference: the new ledgers and
statement card referred to this review artifact before the file existed.  This
review note was added, and the reproduction status was changed from pending to
reviewed.

## Verification

Controller ran:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
cd lean && scripts/lb
cd lean && scripts/sorries
git diff --check
```

The focused module build, full-library build, no-sorry audit, and diff hygiene
check passed through the shared-store `scripts/lb` workflow.  The full build
emitted only unrelated pre-existing Core warnings.
